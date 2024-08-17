import java.util.*;
import soot.*;
import soot.jimple.internal.*;
import soot.toolkits.graph.*;
import soot.toolkits.scalar.*;
import soot.util.Chain;

public class AnalysisTransformer extends BodyTransformer {

    @Override
    protected void internalTransform(Body body, String phaseName, Map<String, String> options) {
        // Create a UnitGraph from the ExceptionalBlockGraph
        UnitGraph unitGraph = new ExceptionalUnitGraph(body);
        // Create a data flow analysis object
        PointsToAnalysisAnalysis analysis = new PointsToAnalysisAnalysis(unitGraph);
        // Print the results
//        analysis.printResults(body);

            List<Integer> finalEscapedObjectsList = new ArrayList<>();
            for (Value value : analysis.alreadyEscapedObjects) {    // take a directly escaped obj
                try {
                finalEscapedObjectsList.addAll(analysis.newObjectsMap.get(value));                  // get the line numbers
                }catch (Exception ignored){
                }
            }
            System.out.print(body.getMethod().getName());
            for (Integer i : finalEscapedObjectsList) {
                System.out.print(" O" + i);
            }
            System.out.println();

    }

    // Custom data flow analysis for points-to information
    private static class PointsToAnalysisAnalysis extends ForwardFlowAnalysis<Unit, FlowSet<Object>> {
        private PointsToAnalysisAnalysis(UnitGraph graph) {
            super(graph);
            doAnalysis();
        }
        @Override
        protected FlowSet<Object> newInitialFlow() {
            return newPointsToSet();
        }
        @Override
        protected FlowSet<Object> entryInitialFlow() {
            return newInitialFlow();
        }
        private FlowSet<Object> newPointsToSet() { // create a new points-to set
            return new ArraySparseSet<>();
        }
        @Override
        protected void merge(FlowSet<Object> in1, FlowSet<Object> in2, FlowSet<Object> out) {
            out.union(in1, in2); //simple union
        }
        @Override
        protected void copy(FlowSet<Object> source, FlowSet<Object> dest) {
            dest.clear();
            dest.union(source);
        }
        // Print the points-to information at each program point
        private void printResults(Body body) {
            System.out.println("********************* Method name :"+body.getMethod().getName());
            Chain<Unit> units = body.getUnits();
            for (Unit unit : units) {
                FlowSet<Object> pointsToSet = getFlowAfter(unit);
                System.out.println(unit + " --> Points-To Set: " + pointsToSet);
            }
        }
        private void addNewObjectsToMap(Value obj,ArrayList<Integer> line){ // utility method
            if(newObjectsMap.containsKey(obj)){         // ref already exist
                ArrayList<Integer> tmp=newObjectsMap.get(obj);
                tmp.addAll(line);
                newObjectsMap.put(obj,tmp); //add new lines to old refs.
            }
            else
                newObjectsMap.put(obj,line);//add new lines to new refs.
        }
        public Map<Value,ArrayList<Integer>> newObjectsMap = new HashMap<>(); //map a ref to obj pointed by it
        public Map<Value,Integer> objectsToLineMap = new HashMap<>();   // maps objs to line no.
        public ArrayList<Value> alreadyEscapedObjects= new ArrayList<>();    // list of already escaped objects
        public ArrayList<Value> args= new ArrayList<>(); // temporary

        @Override
        protected void flowThrough(FlowSet<Object> in, Unit unit, FlowSet<Object> out) {
            out.union(in);
            if (unit instanceof JAssignStmt) {      // assignment stmt
                JAssignStmt assignStmt = (JAssignStmt) unit;
                Value leftOp = assignStmt.getLeftOp();
                Value rightOp = assignStmt.getRightOp();
                if (rightOp instanceof JNewExpr) {      // p=new A()
                    int lineNumber=unit.getJavaSourceStartLineNumber();
                    addNewObjectsToMap(leftOp,new ArrayList<>(lineNumber)); //maps value->set of line no.
                    objectsToLineMap.put(leftOp,lineNumber);  // mapping the new objects to line number
                } else if (leftOp instanceof JInstanceFieldRef) {    // p.f=x
                    ArrayList<Integer> tmp=newObjectsMap.get(rightOp);
                    newObjectsMap.put(leftOp,tmp);   //update the reachability of x
                } else if (rightOp instanceof JInstanceFieldRef) {  // x=p.f
                    //get the obj pointed by f and assign to x
                    newObjectsMap.put(leftOp,newObjectsMap.get(rightOp)); //update the reachability of p.f
                } else if(leftOp instanceof Local && rightOp instanceof Local) {   //x=y
                    addNewObjectsToMap(leftOp, newObjectsMap.get(rightOp)); // assign the object pointed by x to y
                } else if(leftOp instanceof G.Global && rightOp instanceof Local){   //G=y global store
                    alreadyEscapedObjects.add(rightOp);    //directly escaping objects
                } else if (rightOp instanceof JStaticInvokeExpr ) {  //x=op(p1,p2.....pn)
//                    newObjects.put(leftOp,unit.getJavaSourceStartLineNumber());// assign the object returned by op to x
                    args.clear();
                    args= (ArrayList<Value>) ((JStaticInvokeExpr) rightOp).getArgs(); // get the parameters passed to op
                    alreadyEscapedObjects.addAll(args);    //directly escaping objects
                } else if (rightOp instanceof JVirtualInvokeExpr){  //x=y.op(p1,p2.....pn)
//                    newObjects.put(leftOp,unit.getJavaSourceStartLineNumber());// assign the object returned by op to x
                    args.clear();
                    args= (ArrayList<Value>) ((JVirtualInvokeExpr) rightOp).getArgs(); // get the parameters passed to op
                    args.add(((JVirtualInvokeExpr) rightOp).getBase()); // get the caller y
                    alreadyEscapedObjects.addAll(args);    //directly escaping objects
                }
            } else if (unit instanceof JStaticInvokeExpr ) {  //op(p1,p2.....pn)
                args.clear();
                args= (ArrayList<Value>) ((JStaticInvokeExpr) unit).getArgs(); // get the parameters passed to op
                alreadyEscapedObjects.addAll(args);    //directly escaping objects
            } else if (unit instanceof JVirtualInvokeExpr){  //y.op(p1,p2.....pn)
                args.clear();
                args= (ArrayList<Value>) ((JVirtualInvokeExpr) unit).getArgs(); // get the parameters passed to op
                args.add(((JVirtualInvokeExpr) unit).getBase()); // get the caller y
                alreadyEscapedObjects.addAll(args);    //directly escaping objects
            } else if (unit instanceof JReturnStmt) {       //return x
                alreadyEscapedObjects.add(((JReturnStmt) unit).getOp());   // get the x
            }
        }

    }
}