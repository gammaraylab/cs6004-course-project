import java.util.HashMap;
import java.util.List;
import java.util.Set;

import fj.Unit;
import soot.SootMethod;
import soot.jimple.InvokeExpr;
import soot.jimple.internal.JInvokeStmt;

class Element {
    PointsToGraph initGraph; 
    List<String> callerParams;
    String receiverObj;
    int sourceLine;
}
class CallSiteElement {
    // A callsite
    HashMap<InvokeExpr, Element> callsiteMap = new HashMap<>();
}
public class PTGWL {
    static HashMap<SootMethod, PointsToAnalysis> map = new HashMap<>();
    static HashMap<SootMethod, CallSiteElement> elementMap = new HashMap<>();
    
    public static void addCallsiteToUnitMap(SootMethod m, InvokeExpr u, PointsToGraph ptg, List<String> callerParams, String receiverObj, int sourceLine) {
        if (!elementMap.containsKey(m)) elementMap.put(m, new CallSiteElement());
        if (!elementMap.get(m).callsiteMap.containsKey(u)) elementMap.get(m).callsiteMap.put(u, new Element());
        elementMap.get(m).callsiteMap.get(u).initGraph = ptg;
        elementMap.get(m).callsiteMap.get(u).callerParams = callerParams;
        elementMap.get(m).callsiteMap.get(u).receiverObj = receiverObj;
        elementMap.get(m).callsiteMap.get(u).sourceLine = sourceLine;
    }

}