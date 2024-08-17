import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import fj.P;
import soot.Body;
import soot.PatchingChain;
import soot.Scene;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.BinopExpr;
import soot.jimple.ClassConstant;
import soot.jimple.Constant;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.NullConstant;
import soot.jimple.ParameterRef;
import soot.jimple.StaticFieldRef;
import soot.jimple.ThisRef;
import soot.jimple.internal.JArrayRef;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JBreakpointStmt;
import soot.jimple.internal.JCastExpr;
import soot.jimple.internal.JCaughtExceptionRef;
import soot.jimple.internal.JDynamicInvokeExpr;
import soot.jimple.internal.JEnterMonitorStmt;
import soot.jimple.internal.JExitMonitorStmt;
import soot.jimple.internal.JGotoStmt;
import soot.jimple.internal.JIdentityStmt;
import soot.jimple.internal.JIfStmt;
import soot.jimple.internal.JInstanceFieldRef;
import soot.jimple.internal.JInterfaceInvokeExpr;
import soot.jimple.internal.JInvokeStmt;
import soot.jimple.internal.JLengthExpr;
import soot.jimple.internal.JLookupSwitchStmt;
import soot.jimple.internal.JNewArrayExpr;
import soot.jimple.internal.JNewExpr;
import soot.jimple.internal.JNopStmt;
import soot.jimple.internal.JRetStmt;
import soot.jimple.internal.JReturnStmt;
import soot.jimple.internal.JReturnVoidStmt;
import soot.jimple.internal.JSpecialInvokeExpr;
import soot.jimple.internal.JStaticInvokeExpr;
import soot.jimple.internal.JTableSwitchStmt;
import soot.jimple.internal.JThrowStmt;
import soot.jimple.internal.JVirtualInvokeExpr;
import soot.jimple.internal.JimpleLocal;
import soot.jimple.toolkits.callgraph.Edge;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.ClassicCompleteUnitGraph;
import soot.toolkits.graph.UnitGraph;
import soot.toolkits.scalar.LiveLocals;
import soot.toolkits.scalar.SimpleLiveLocals;

public class PointsToAnalysis {
  PatchingChain<Unit> units;
  UnitGraph uGraph;
  String methodName;

  PointsToGraph initGraph;
  HashMap<Unit, PointsToGraph> outSets;
  Set<String> alwaysLive = new HashSet<>();

  LiveLocals lva;

  HashMap<String, Integer> elimination = new HashMap<>();

  final boolean ASSERT_DEBUG = true;

  PointsToAnalysis(Body body, String methodName) {
    this.uGraph = new ClassicCompleteUnitGraph(body);
    this.units = body.getUnits();
    this.methodName = methodName;
    this.initGraph = new PointsToGraph();
    this.lva = new SimpleLiveLocals(new BriefUnitGraph(body));
    for (Unit u : units) {
      if (u instanceof JIdentityStmt idenStmt) {
        Value leftVal = idenStmt.leftBox.getValue();
        Value rightVal = idenStmt.rightBox.getValue();

        String heapObjName = null;
        String wrappedStackVal = null;

        // a = @parameter n
        if (leftVal instanceof JimpleLocal stackVal && rightVal instanceof ParameterRef) {
          ParameterRef paramref = (ParameterRef) idenStmt.rightBox.getValue();
          heapObjName = wrapString("@param_" + paramref.getIndex());
          wrappedStackVal = wrapString(stackVal.getName());
        }

        // a = @thisptr
        else if (leftVal instanceof JimpleLocal stackVal && rightVal instanceof ThisRef) {
          heapObjName = wrapString("@this");
          wrappedStackVal = wrapString(stackVal.getName());
        }

        // a = @exception
        else if (leftVal instanceof JimpleLocal stackVal && rightVal instanceof JCaughtExceptionRef) {
          heapObjName = wrapString("@caughtexception_" + idenStmt.getJavaSourceStartLineNumber());
          wrappedStackVal = wrapString(stackVal.getName());
        }

        else if (ASSERT_DEBUG) {
          System.err.println("Unhandled case reached in 'IdentityStatement' : " + idenStmt.getClass());
          System.exit(1);
        }

        // Update points to graph
        if (wrappedStackVal != null) {
          this.initGraph.handleSimpleNewStatement(wrappedStackVal, heapObjName);
          this.initGraph.objectsToMark.add(heapObjName);
        }
      }
    }
  }

  PointsToAnalysis(Body body, String methodName, PointsToGraph initGraph, Set<String> alwaysLive) {
    this.uGraph = new ClassicCompleteUnitGraph(body);
    this.units = body.getUnits();
    this.methodName = methodName;
    this.initGraph = initGraph;
    this.alwaysLive = alwaysLive;
    this.lva = new SimpleLiveLocals(new BriefUnitGraph(body));
  }

  public static PointsToGraph getProcessedPTG(PatchingChain<Unit> units, PointsToGraph initial,
      List<String> callerParams, String receiverObj, Set<String> alwaysLiveObjs) {
    PointsToGraph result = initial.clone();
    HashMap<String, Set<String>> oldStackMapping = result.stack;
    result.stack = new HashMap<>();
    alwaysLiveObjs.addAll(initial.computeClosure());
    // Process formals
    for (Unit u : units) {
      if (u instanceof JIdentityStmt idenStmt) {
        Value leftVal = idenStmt.leftBox.getValue();
        Value rightVal = idenStmt.rightBox.getValue();

        // a = @parameter n
        if (leftVal instanceof JimpleLocal stackVal && rightVal instanceof ParameterRef) {
            ParameterRef paramref = (ParameterRef) idenStmt.rightBox.getValue();

          String wrappedStackVal = wrapString(stackVal.getName());
          if (callerParams.size() <= paramref.getIndex()) {
            System.err.println("Invalid index provided : " + paramref.getIndex() + " " + callerParams);
            System.exit(1);
          }
          String stackNameInInitGraph = callerParams.get(paramref.getIndex());

          if (stackNameInInitGraph != null) {
            alwaysLiveObjs.addAll(oldStackMapping.get(stackNameInInitGraph));
            result.stack.put(wrappedStackVal, oldStackMapping.get(stackNameInInitGraph));
          }
        }

        // a = @thisptr
        else if (leftVal instanceof JimpleLocal && rightVal instanceof ThisRef) {
          if (receiverObj == null) {
            JimpleLocal stackVal = (JimpleLocal) leftVal;
            String heapObjName = wrapString("@this");
            String wrappedStackVal = wrapString(stackVal.getName());
            result.handleSimpleNewStatement(wrappedStackVal, heapObjName);
            alwaysLiveObjs.add(heapObjName);
          } else {
            JimpleLocal stackVal = (JimpleLocal) leftVal;
            String wrappedStackVal = wrapString(stackVal.getName());
            if (oldStackMapping.containsKey(receiverObj)) {
              result.stack.put(wrappedStackVal, oldStackMapping.get(receiverObj));
              alwaysLiveObjs.addAll(oldStackMapping.get(receiverObj));
            }
          }
        }
      }
    }
    return result;
  }

  public static String wrapString(String s) {
    return "\"" + s + "\"";
  }

  // 1.
  // Statement: return a
  // Action: A stack variable at line return points to whatever the return var
  // points to
  private void handleReturnStmt(JReturnStmt retStmt, PointsToGraph ptg) {
    Value val = retStmt.getOp();
    if (val instanceof JimpleLocal stackVal) {
      String retName = wrapString("@return_" + retStmt.getJavaSourceStartLineNumber());
      String wrappedStackVal = wrapString(stackVal.getName());
      ptg.handleCopyStatement(retName, wrappedStackVal);
    }

    else if (val instanceof Constant) {
      /* NONE */
    }

    else if (ASSERT_DEBUG) {
      System.err.println("Unhandled case reached in 'JReturnStmt' : " + retStmt.getClass());
      System.exit(1);
    }
  }

  // 2.
  // Statement: return
  // Action: NONE
  private void handleReturnVoidStmt(JReturnVoidStmt retVoidStmt, PointsToGraph ptg) {
  }

  // 3.
  // Statement: a = @this, a = @parameter, a = @caughtexception
  // Action: NONE
  private void handleIdentityStmt(JIdentityStmt idenStmt, PointsToGraph ptg) {
  }

  private PointsToGraph handleInvokeExpr(InvokeExpr invokeExpr, PointsToGraph ptg, Unit u) {
    PointsToGraph result = new PointsToGraph();
    if (invokeExpr instanceof JDynamicInvokeExpr) {
      /* NONE */
    }

    else if (invokeExpr instanceof JInterfaceInvokeExpr) {
      /* TODO */
    }

    else if (invokeExpr instanceof JSpecialInvokeExpr) {
      /* NONE */
    }

    else if (invokeExpr instanceof JStaticInvokeExpr) {
      SootMethod outputMethod = invokeExpr.getMethod();
      List<String> callerParams = new ArrayList<>();
      for (int i = 0; i < invokeExpr.getArgCount(); i++) {
        Value argValue = invokeExpr.getArg(i);
        if (argValue instanceof JimpleLocal) {
          callerParams.add(i, wrapString(((JimpleLocal) argValue).getName()));
        } else {
          callerParams.add(i, null);
        }
      }

      PointsToGraph clonePTG = ptg.clone();
      lva.getLiveLocalsBefore(u).forEach((s) -> {
        clonePTG.objectsToMark.add(PointsToGraph.wrapString(s.getName()));
      });
      clonePTG.objectsToMark.addAll(alwaysLive);
      clonePTG.computeClosure();
      for (String stackVar : clonePTG.stack.keySet()) {
        clonePTG.objectsToMark.remove(stackVar);
      }

      Set<String> alwaysLiveObjs = new HashSet<>();
      PTGWL.addCallsiteToUnitMap(outputMethod, invokeExpr, clonePTG, callerParams, null,
          u.getJavaSourceStartLineNumber());
      PointsToGraph init = PointsToAnalysis.getProcessedPTG(outputMethod.getActiveBody().getUnits(), clonePTG,
          callerParams, null, alwaysLiveObjs);

      PointsToAnalysis pta = new PointsToAnalysis(outputMethod.getActiveBody(),
          outputMethod.getDeclaringClass().getName() + "_" + outputMethod.getName(), init,
          alwaysLiveObjs);

      try {
        pta.doAnalysis();
      } catch (Exception e) {
        e.printStackTrace();
      }
      result = pta.getPTGSummary();
    }

    else if (invokeExpr instanceof JVirtualInvokeExpr) {
      Iterator<Edge> edges = Scene.v().getCallGraph().edgesOutOf(u);
      while (edges.hasNext()) {
        Edge edge = edges.next();
        SootMethod targetMethod = edge.tgt();
        // Recursively explore callee methods
        if (!targetMethod.isJavaLibraryMethod()) {
          List<String> callerParams = new ArrayList<>();
          for (int i = 0; i < invokeExpr.getArgCount(); i++) {
            Value argValue = invokeExpr.getArg(i);
            if (argValue instanceof JimpleLocal) {
              callerParams.add(i, wrapString(((JimpleLocal) argValue).getName()));
            } else {
              callerParams.add(i, null);
            }
          }
          JVirtualInvokeExpr virtualInvokeExpr = (JVirtualInvokeExpr) invokeExpr;
          String receiverObj = wrapString(((JimpleLocal) virtualInvokeExpr.getBase()).getName());

          PointsToGraph clonePTG = ptg.clone();
          lva.getLiveLocalsBefore(u).forEach((s) -> {
            clonePTG.objectsToMark.add(PointsToGraph.wrapString(s.getName()));
          });
          clonePTG.objectsToMark.addAll(alwaysLive);
          clonePTG.computeClosure();
          for (String stackVar : clonePTG.stack.keySet()) {
            clonePTG.objectsToMark.remove(stackVar);
          }

          Set<String> alwaysLiveObjs = new HashSet<>();
          PTGWL.addCallsiteToUnitMap(targetMethod, invokeExpr, clonePTG, callerParams, receiverObj,
              u.getJavaSourceStartLineNumber());
          PointsToGraph init = PointsToAnalysis.getProcessedPTG(targetMethod.getActiveBody().getUnits(), clonePTG,
              callerParams, receiverObj, alwaysLiveObjs);

          PointsToAnalysis pta = new PointsToAnalysis(targetMethod.getActiveBody(),
              targetMethod.getDeclaringClass().getName() + "_" + targetMethod.getName(), init,
              alwaysLiveObjs);

          try {
            pta.doAnalysis();
          } catch (Exception e) {
            e.printStackTrace();
          }
          result.add(pta.getPTGSummary());
        }
      }
    }

    else if (ASSERT_DEBUG) {
      System.err.println("Unhandled case reached in 'InvokeStatement'");
      System.exit(1);
    }

    return result;
  }

  // 4.
  // Statement: InvokeStatement
  // Action: At invoke statements
  private void handleInvokeStmt(JInvokeStmt invokeStmt, PointsToGraph ptg) {
    InvokeExpr invokeExpr = ((JInvokeStmt) invokeStmt).getInvokeExpr();
    PointsToGraph resultPTG = handleInvokeExpr(invokeExpr, ptg, (Unit) invokeStmt);
    resultPTG.stack.clear();
    ptg.add(resultPTG);
  }

  // 5.
  // Statement: goto X
  // Action: NONE
  private void handleGotoStmt(JGotoStmt gotoStmt, PointsToGraph ptg) {
  }

  // 6.
  // Statement: if cond == true goto X
  // Action: NONE
  private void handleIfStmt(JIfStmt ifStmt, PointsToGraph ptg) {
  }

  // 7.
  // Statement: EnterMonitorStmt
  // Action: NONE
  private void handleEnterMonitor(JEnterMonitorStmt enterMonitorStmt, PointsToGraph ptg) {
  }

  // 8.
  // Statement: JExitMonitorStmt
  // Action: NONE
  private void handleExitMonitor(JExitMonitorStmt exitMonitorStmt, PointsToGraph ptg) {
  }

  // 9.
  // Statement: JNopStmt
  // Action: NONE
  private void handleNopStmt(JNopStmt jNopStmt, PointsToGraph ptg) {
  }

  // 10.
  // Statement: throw X
  // Action: Object being thrown escapes
  private void handleThrowStmt(JThrowStmt jThrowStmt, PointsToGraph ptg) {

    Value val = jThrowStmt.getOp();
    if (val instanceof JimpleLocal stackVal) {
      String retName = wrapString("@throw_" + jThrowStmt.getJavaSourceStartLineNumber());
      String wrappedStackVal = wrapString(stackVal.getName());
      ptg.handleAssignmentToGlobal(retName, wrappedStackVal);
    }

    else if (val instanceof Constant) {
      /* NONE */
    }

    else if (ASSERT_DEBUG) {
      System.err.println("Unhandled case reached in 'JReturnStmt'");
      System.exit(1);
    }
  }

  // 11.
  // Statement: JBreakpointStmt
  // Action: NONE
  private void handleBreakpointStmt(JBreakpointStmt jBreakpointStmt, PointsToGraph ptg) {
  }

  // 12.
  // Statement: JAssignStmt
  // Action: Handle all assignment cases
  private void handleAssignmentStmt(JAssignStmt stmnt, PointsToGraph ptg) {
    // a = new A()
    if (stmnt.leftBox.getValue() instanceof JimpleLocal stackVal && stmnt.rightBox.getValue() instanceof JNewExpr) {
      String heapObjName = "O" + stmnt.getJavaSourceStartLineNumber();
      String wrappedStackVal = wrapString(stackVal.getName());
      ptg.handleSimpleNewStatement(wrappedStackVal, heapObjName);
    }
    // a.f = b
    else if (stmnt.leftBox.getValue() instanceof JInstanceFieldRef fieldref
        && stmnt.rightBox.getValue() instanceof JimpleLocal stackVal) {
      String wrappedStackVal = wrapString(stackVal.getName());
      String wrapped_a = wrapString(fieldref.getBase().toString());
      String wrapped_f = wrapString(fieldref.getField().getName());
      ptg.handleStoreStatement(wrapped_a, wrapped_f, wrappedStackVal);
    }
    // a = b.f
    else if (stmnt.leftBox.getValue() instanceof JimpleLocal stackVal
        && stmnt.rightBox.getValue() instanceof JInstanceFieldRef fieldref) {
      String wrappedStackVal = wrapString(stackVal.getName());
      String wrapped_b = wrapString(fieldref.getBase().toString());
      String wrapped_f = wrapString(fieldref.getField().getName());

      ptg.handleLoadStatement(wrappedStackVal, wrapped_b, wrapped_f);
    }
    // a = b
    else if (stmnt.leftBox.getValue() instanceof JimpleLocal stackVal1
        && stmnt.rightBox.getValue() instanceof JimpleLocal stackVal2) {
      String wrappedStackVal1 = wrapString(stackVal1.getName());
      String wrappedStackVal2 = wrapString(stackVal2.getName());
      ptg.handleCopyStatement(wrappedStackVal1, wrappedStackVal2);
    }
    // global = a
    else if (stmnt.leftBox.getValue() instanceof StaticFieldRef staticFieldref
        && stmnt.rightBox.getValue() instanceof JimpleLocal stackVal) {

        String wrappedGlobal = wrapString(staticFieldref.getField().getName());
      String wrappedStackVal = wrapString(stackVal.getName());

      ptg.handleAssignmentToGlobal(wrappedGlobal, wrappedStackVal);
      // ptg.objectsToMark.add(wrappedGlobal);
    }
    // a = global
    else if (stmnt.leftBox.getValue() instanceof JimpleLocal stackVal
        && stmnt.rightBox.getValue() instanceof StaticFieldRef staticFieldref) {

        String wrappedStackVal = wrapString(stackVal.getName());
      String wrappedGlobal = wrapString(staticFieldref.getField().getName());

      ptg.handleAssignmentFromGlobal(wrappedStackVal, wrappedGlobal);
      // ptg.objectsToMark.add(wrappedGlobal);
    }
    // a = lengthof b
    else if (stmnt.leftBox.getValue() instanceof JimpleLocal
        && stmnt.rightBox.getValue() instanceof JLengthExpr) {
      // Ignore
    }
    // a = null
    else if (stmnt.leftBox.getValue() instanceof JimpleLocal stackVal
        && stmnt.rightBox.getValue() instanceof NullConstant) {
        String wrappedStackVal = wrapString(stackVal.getName());
      ptg.handleSimpleNULLStatement(wrappedStackVal);
    }
    // a.f = null
    else if (stmnt.leftBox.getValue() instanceof JInstanceFieldRef fieldref
        && stmnt.rightBox.getValue() instanceof NullConstant) {
        String wrapped_a = wrapString(fieldref.getBase().toString());
      String wrapped_f = wrapString(fieldref.getField().getName());

      ptg.handleNULLStoreStatement(wrapped_a, wrapped_f);
    }
    // a = b.foo()
    else if (stmnt.leftBox.getValue() instanceof JimpleLocal
        && stmnt.rightBox.getValue() instanceof JInterfaceInvokeExpr) {
      /* TODO */
    }
    // a = <virtualInvoke>
    else if (stmnt.leftBox.getValue() instanceof JimpleLocal stackVal
        && stmnt.rightBox.getValue() instanceof JVirtualInvokeExpr) {
      InvokeExpr invokeExpr = ((JVirtualInvokeExpr) stmnt.rightBox.getValue());
      PointsToGraph resultPTG = handleInvokeExpr(invokeExpr, ptg, (Unit) stmnt);
        String wrappedStackVal = wrapString(stackVal.getName());
      HashMap<String, Set<String>> oldStack = resultPTG.stack;
      resultPTG.stack = new HashMap<>();
      resultPTG.stack.put(wrappedStackVal, oldStack.get("return"));
      ptg.add(resultPTG);
    }

    // a = new Array[]
    else if (stmnt.leftBox.getValue() instanceof JimpleLocal stackVal
        && stmnt.rightBox.getValue() instanceof JNewArrayExpr) {
        String wrappedStackVal = wrapString(stackVal.getName());
      String heapObjName = "O" + stmnt.getJavaSourceStartLineNumber();
      String arrayStore = "A" + stmnt.getJavaSourceStartLineNumber();
      ptg.handleArrayNewStatement(wrappedStackVal, heapObjName, arrayStore);
    }

    // [any] = constant
    else if (stmnt.rightBox.getValue() instanceof Constant) {
      /* ignore */
    }

    // [any] = a binop b
    else if (stmnt.rightBox.getValue() instanceof BinopExpr) {
      /* ignore */
    }

    // a = arr[10]
    else if (stmnt.leftBox.getValue() instanceof JimpleLocal stackVal
        && stmnt.rightBox.getValue() instanceof JArrayRef arrayRef) {

      final String STAR_FIELD = "\"*\"";
      String wrappedStackVal = wrapString(stackVal.getName());
      String wrappedArrayBase = wrapString(arrayRef.getBase().toString());

      ptg.handleLoadStatement(wrappedStackVal, wrappedArrayBase, STAR_FIELD);
    }
    // arr[10] = b
    else if (stmnt.leftBox.getValue() instanceof JArrayRef arrayRef
        && stmnt.rightBox.getValue() instanceof JimpleLocal stackVal) {

      final String STAR_FIELD = "\"*\"";
      String wrappedStackVal = wrapString(stackVal.getName());
      String wrappedArrayBase = wrapString(arrayRef.getBase().toString());

      ptg.handleStoreStatement(wrappedArrayBase, STAR_FIELD, wrappedStackVal);
    }
    // arr[10] = class "Ltestcase/Test4;"
    else if (stmnt.leftBox.getValue() instanceof JArrayRef arrayRef
        && stmnt.rightBox.getValue() instanceof ClassConstant classConst) {

      String wrappedArrayBase = wrapString(arrayRef.getBase().toString());
      String classConstStr = wrapString(classConst.getValue());
      String classConstStrObj = wrapString("@" + classConst.getValue());

      ptg.stackStrongUpdate(classConstStr, classConstStrObj);
      final String STAR_FIELD = "\"*\"";
      ptg.handleStoreStatement(wrappedArrayBase, STAR_FIELD, classConstStr);

      // ptg.objectsToMark.add(classConstStr);
      // ptg.objectsToMark.add(classConstStrObj);

    }
    // r0.f = 10
    else if (stmnt.leftBox.getValue() instanceof JInstanceFieldRef
        && stmnt.rightBox.getValue() instanceof IntConstant) {
      // ignore
    }
    // a = <static invoke>
    else if (stmnt.leftBox.getValue() instanceof JimpleLocal stackVal
        && stmnt.rightBox.getValue() instanceof JStaticInvokeExpr) {
      InvokeExpr invokeExpr = ((JStaticInvokeExpr) stmnt.rightBox.getValue());
      PointsToGraph resultPTG = handleInvokeExpr(invokeExpr, ptg, stmnt);
      String wrappedStackVal = wrapString(stackVal.getName());
      HashMap<String, Set<String>> oldStack = resultPTG.stack;
      resultPTG.stack = new HashMap<>();
      resultPTG.stack.put(wrappedStackVal, oldStack.get("return"));
      ptg.add(resultPTG);
    }
    // a = (A) b
    else if (stmnt.leftBox.getValue() instanceof JimpleLocal s
        && stmnt.rightBox.getValue() instanceof JCastExpr castExpr) {
      String w1 = wrapString(s.getName());
      String w2 = wrapString(castExpr.getOp().toString());
      ptg.handleCopyStatement(w1, w2);
    }

    else if (ASSERT_DEBUG) {
      System.err.println("Unhandled statement reached 'JAssignStmt'");
      System.err.println(stmnt);

      System.err.println("Left: " + stmnt.leftBox.getValue().getClass() + ", Right: "
          + stmnt.rightBox.getValue().getClass());

    }
  }

  // 13.
  // Statement: JLookupSwitchStmt
  // Action: NONE
  private void handleLookupSwitchStmt(JLookupSwitchStmt jLookupSwitchStmt, PointsToGraph ptg) {
  }

  // 14.
  // Statement: JTableSwitchStmt
  // Action: NONE
  private void handleTableSwitchStmt(JTableSwitchStmt jTableSwitchStmt, PointsToGraph ptg) {
  }

  // 15.
  // Statement: JRetStmt
  // Action: NONE
  private void handleRetStmt(JRetStmt jRetStmt, PointsToGraph ptg) {
  }


  private void flowFunction(Unit u, PointsToGraph ptg) {

    // 1. ReturnStmt<JReturnStmt>
    if (u instanceof JReturnStmt)
      handleReturnStmt((JReturnStmt) u, ptg);
    // 2. ReturnVoid<JReturnVoidStmt>
    else if (u instanceof JReturnVoidStmt)
      handleReturnVoidStmt((JReturnVoidStmt) u, ptg);
    // 3. IdentityStmt<JIdentityStmt>
    else if (u instanceof JIdentityStmt)
      handleIdentityStmt((JIdentityStmt) u, ptg);
    // 4. InvokeStmt<JInvokeStmt> === invoke InvokeExpr
    else if (u instanceof JInvokeStmt)
      handleInvokeStmt((JInvokeStmt) u, ptg);
    // 5. gotoStmt<JGotoStmt>
    else if (u instanceof JGotoStmt)
      handleGotoStmt((JGotoStmt) u, ptg);
    // 6. ifStmt<JIfStmt>
    else if (u instanceof JIfStmt)
      handleIfStmt((JIfStmt) u, ptg);
    // 7. MonitorEnterStmt<JEnterMonitorStmt>
    else if (u instanceof JEnterMonitorStmt)
      handleEnterMonitor((JEnterMonitorStmt) u, ptg);
    // 8. MonitorExitStmt<JExitMonitorStmt>
    else if (u instanceof JExitMonitorStmt)
      handleExitMonitor((JExitMonitorStmt) u, ptg);
    // 9. nopStmt<JNopStmt>
    else if (u instanceof JNopStmt)
      handleNopStmt((JNopStmt) u, ptg);
    // 10. ThrowStmt<JThrowStmt>
    else if (u instanceof JThrowStmt)
      handleThrowStmt((JThrowStmt) u, ptg);
    // 11. BreakpointStmt<JBreakpointStmt>
    else if (u instanceof JBreakpointStmt)
      handleBreakpointStmt((JBreakpointStmt) u, ptg);
    // 12. AssignmentStatement<JAssignStmt>
    else if (u instanceof JAssignStmt)
      handleAssignmentStmt((JAssignStmt) u, ptg);
    // 13. LookupSwitch<JLookupSwitchStmt>
    else if (u instanceof JLookupSwitchStmt)
      handleLookupSwitchStmt((JLookupSwitchStmt) u, ptg);
    // 14. TableSwitch<JTableSwitchStmt>
    else if (u instanceof JTableSwitchStmt)
      handleTableSwitchStmt((JTableSwitchStmt) u, ptg);
    // 15. JRetStmt -- deprecated
    // Wiki(https://en.wikipedia.org/wiki/List_of_Java_bytecode_instructions#endnote_Deprecated)
    else if (u instanceof JRetStmt)
      handleRetStmt((JRetStmt) u, ptg);

    else if (ASSERT_DEBUG) {
      System.err.println("Unhandled statement reached '" + u.getClass() + "'");
      assert (false);
    }

    if (u instanceof JReturnStmt) {
      ptg.stack.keySet().forEach((s) -> {
        if (s.contains("@return")) {
          ptg.objectsToMark.add(s);
        }
      });
    }
    lva.getLiveLocalsAfter(u).forEach((s) -> {
      ptg.objectsToMark.add(PointsToGraph.wrapString(s.getName()));
    });
    ptg.objectsToMark.addAll(alwaysLive);
    ptg.computeClosure();
    Set<String> usedObjs = ptg.computeClosure();
    Set<String> GC = ptg.getAllHeapObjs();
    GC.removeAll(usedObjs);
    GC.forEach((h) -> {
      ptg.eliminateHeapObj(h);
      elimination.put(h, u.getJavaSourceStartLineNumber());
      ptg.collectedObjects.add(h);
    });
  }

  // ***********************************************************************************************

  PointsToGraph PTGSummary = null;

  public PointsToGraph getPTGSummary() {
    return PTGSummary;
  }

  public void doAnalysis() throws Exception {

    List<Unit> worklist = new ArrayList<>();
    outSets = new HashMap<>();

    // Initialize flowvalues
    for (Unit u : units) {
      outSets.put(u, new PointsToGraph());
    }

    // First interation over the CFG, worklist initialization
    for (Unit currUnit : units) {
      PointsToGraph currentFlowSet = new PointsToGraph();
      PointsToGraph old = outSets.get(currUnit);

      // Starting point of the function will not have any predecessors, we will take a
      // meet of all the incoming PTGs
      if (uGraph.getPredsOf(currUnit).isEmpty())
        currentFlowSet.add(initGraph);

      // Check incoming edges
      for (Unit incoming : uGraph.getPredsOf(currUnit)) {
        currentFlowSet.add(outSets.get(incoming));
      }

      flowFunction(currUnit, currentFlowSet);

      // Add successors to worklist
      if (!old.equals(currentFlowSet)) {
        outSets.put(currUnit, currentFlowSet);
        worklist.addAll(uGraph.getSuccsOf(currUnit));
      }
    }

    while (!worklist.isEmpty()) {
      // Pop one unit from the worklist
      Unit currUnit = worklist.getFirst();
      worklist.remove(currUnit);

      PointsToGraph currentFlowSet = new PointsToGraph();
      PointsToGraph old = outSets.get(currUnit);

      // Starting point of the function will not have any predecessors, we will take a
      // meet of all the incoming PTGs
      if (uGraph.getPredsOf(currUnit).isEmpty()) {
        currentFlowSet.add(initGraph);
      }

      // Check incoming edges
      for (Unit incoming : uGraph.getPredsOf(currUnit)) {
        currentFlowSet.add(outSets.get(incoming));
      }

      flowFunction(currUnit, currentFlowSet);

      // Add successors to worklist
      if (!old.equals(currentFlowSet)) {
        outSets.put(currUnit, currentFlowSet);
        worklist.addAll(uGraph.getSuccsOf(currUnit));
      }

    }

    // Merge all return statements
    PointsToGraph summary = new PointsToGraph();
    for (Unit u : units) {
      if (u instanceof JReturnVoidStmt || u instanceof JRetStmt || u instanceof JReturnStmt) {
        summary.add(outSets.get(u));
      }
    }

    // clear local stack mappings
    Set<String> finalStackReturns = new HashSet<>();
    HashMap<String, Set<String>> oldStack = summary.stack;
    summary.stack = new HashMap<>();
    for (String stackVar : oldStack.keySet()) {
      if (stackVar.contains("@return")) {
        finalStackReturns.addAll(oldStack.get(stackVar));
      }
    }
    if (!finalStackReturns.isEmpty())
      summary.stack.put("return", finalStackReturns);

    // store union of PTGs are return statements
    PTGSummary = summary;
  }
}
