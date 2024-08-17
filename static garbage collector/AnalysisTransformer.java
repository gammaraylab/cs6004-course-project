import java.util.*;
import soot.*;
import soot.jimple.InvokeExpr;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;

public class AnalysisTransformer extends SceneTransformer {
    static CallGraph cg;

    @Override
    protected void internalTransform(String arg0, Map<String, String> arg1) {
        Set<SootMethod> methods = new HashSet<>();
        cg = Scene.v().getCallGraph();
        SootMethod mainMethod = Scene.v().getMainMethod();
        // Get the list of methods reachable from the main method
        getlistofMethods(mainMethod, methods);

        PTGWL.map.put(mainMethod, new PointsToAnalysis(mainMethod.getActiveBody(), mainMethod.getDeclaringClass().getName() + "_" + mainMethod.getName()));

        // Process main method's PTG
        try {
            PTGWL.map.get(mainMethod).doAnalysis();
        } catch (Exception e) {
            e.printStackTrace();
        }

        for (SootMethod m : methods) {
            if (m != mainMethod) {
                if (!PTGWL.elementMap.containsKey(m))
                    continue;

                CallSiteElement cselement = PTGWL.elementMap.get(m);
                PointsToGraph init = new PointsToGraph();
                Set<String> alwaysLiveObjs = new HashSet<>();
                for (InvokeExpr ie : cselement.callsiteMap.keySet()) {
                    Element e = cselement.callsiteMap.get(ie);

                    PointsToGraph modifiedPTG = PointsToAnalysis.getProcessedPTG(m.getActiveBody().getUnits(),
                            e.initGraph, e.callerParams, e.receiverObj, alwaysLiveObjs);
                    init.add(modifiedPTG);
                }

                PointsToAnalysis pta = new PointsToAnalysis(m.getActiveBody(), m.getDeclaringClass().getName() + "_" + m.getName(), init, alwaysLiveObjs);
                try {
                    pta.doAnalysis();
                } catch (Exception e) {
                    e.printStackTrace();
                }

                PTGWL.map.put(m, pta);
            }

        }

        HashMap<String, Integer> maximalEliminationMap = new HashMap<>();
        List<String> methodListSorted = new ArrayList<>();
        

        for (SootMethod m : methods) {
            if (!PTGWL.map.containsKey(m)) {
                continue;
            }
            methodListSorted.add(m.getDeclaringClass().getName() + ":" + m.getName());
            for (String heapObj : PTGWL.map.get(m).elimination.keySet()) {
                Integer currSol = PTGWL.map.get(m).elimination.get(heapObj);
                if (maximalEliminationMap.containsKey(heapObj)) {
                    if (maximalEliminationMap.get(heapObj) < currSol) {
                        maximalEliminationMap.put(heapObj, currSol);
                    }
                } else {
                    maximalEliminationMap.put(heapObj, currSol);
                }
            }
        }
        Collections.sort(methodListSorted);

        HashMap<String, Set<String>> finalRes = new HashMap<>();

        for (SootMethod m : methods) {
            if (!PTGWL.map.containsKey(m)) {
                continue;
            }
            String key = m.getDeclaringClass().getName() + ":" + m.getName();
            finalRes.put(key, new HashSet<>());
            for (String heapObj : PTGWL.map.get(m).elimination.keySet()) {
                Integer currSol = PTGWL.map.get(m).elimination.get(heapObj);
                if (maximalEliminationMap.get(heapObj) <= currSol) {
                    if (heapObj.startsWith("O"))
                        finalRes.get(key).add(heapObj.substring(1) + ":" + currSol);
                }
            }
        }

        for (String m : methodListSorted) {
            System.out.print(m + " ");
            if (!finalRes.get(m).isEmpty()) {
                List<String> sortedSoln = new ArrayList<>(finalRes.get(m));
                Collections.sort(sortedSoln);
                for (String so : sortedSoln) {
                    System.out.print(so + " ");
                }
            }
            System.out.println();
        }

        HashMap<String, String> r = new HashMap<>();
        for (SootMethod m : methods) {
            String key = m.getDeclaringClass().getName() + ":" + m.getName();
            if (finalRes.containsKey(key)) {
                List<String> rrr = new ArrayList<>(finalRes.get(key));
                Collections.sort(rrr);
                StringBuilder rrrr = new StringBuilder();
                for (String so : rrr) {
                    rrrr.append(so).append(" ");
                }
                r.put(m.getDeclaringClass().getName() + "_" + m.getName(), key + " " + rrrr.toString());
            }
        }
    }

    private static void getlistofMethods(SootMethod method, Set<SootMethod> reachableMethods) {
        // Avoid revisiting methods
        if (reachableMethods.contains(method))
            return;
        // Add the method to the reachable set
        reachableMethods.add(method);
        // Iterate over the edges originating from this method
        Iterator<Edge> edges = Scene.v().getCallGraph().edgesOutOf(method);
        while (edges.hasNext()) {
            Edge edge = edges.next();
            SootMethod targetMethod = edge.tgt();
            // Recursively explore callee methods
            if (!targetMethod.isJavaLibraryMethod())
                getlistofMethods(targetMethod, reachableMethods);
        }
    }
}
