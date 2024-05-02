/**
 * @name Find data flows from a credential source to a logging sink
 * @description Find data flows from a credential source to a logging sink
 * @id cs/credential-logging
 * @kind path-problem
 * @problem.severity error
 * @security-severity 9.8
 * @precision high
 * @tags security
 *       cwe-532
 */

 import csharp
 import semmle.code.csharp.dataflow.TaintTracking
 import semmle.code.csharp.commons.Loggers
 
 private class Logging extends DataFlow::Node {
   Logging() {
     exists(MethodCall call |
       call.getQualifier().getType() instanceof LoggerType and
       this.asExpr() = call.getAnArgument()
     )
   }
 }
 
 private class CredentialVar extends Assignable {
   pragma[noinline]
   CredentialVar() {
     exists(string name | name = this.getName() |
       name.regexpMatch("(?i).*pass(wd|word|code|phrase)(?!.*question).*")
       or
       name.regexpMatch("(?i).*(puid|username|userid)(?!.*(characters|claimtype)).*")
       or
       name.regexpMatch("(?i).*(cert)(?!.*(format|name)).*")
     )
   }
 }
 
 class CredentialsSource extends DataFlow::Node {
   CredentialsSource() {
     exists(CredentialVar cv | this.asExpr() = cv.getAnAccess())
     or
     exists(Variable v, CredentialVar cv, PropertyAccess pa, VariableAccess va |
       this.asExpr() = va and
       pa.getProperty() = cv and
       pa.getQualifier*() = va and
       va = v.getAnAccess()
     )
   }
 }
 
 module LoggingConfig implements DataFlow::ConfigSig {
   predicate isSource(DataFlow::Node source) { source instanceof CredentialsSource }
 
   predicate isSink(DataFlow::Node sink) { sink instanceof Logging }
 }
 
 module LoggingFlow = TaintTracking::Global<LoggingConfig>;
 import LoggingFlow::PathGraph
 
 /* control flow reaches */
 // from CredentialsSource source, Logging sink
 // where sink.asExpr().reachableFrom(source.asExpr())
 // select source, sink
 
 /* partial flow */
 // int explorationLimit() { result = 20 }
 // module LoggingFlowPartial = LoggingFlow::FlowExplorationFwd<explorationLimit/0>;
 // import LoggingFlowPartial::PartialPathGraph
 // from LoggingFlowPartial::PartialPathNode source, LoggingFlowPartial::PartialPathNode node
 // where LoggingFlowPartial::partialFlow(source, node, _)
 // select node, "We reached this node from $@", source, "this source"
 
 /* data flow */
 from LoggingFlow::PathNode source, LoggingFlow::PathNode sink
 where LoggingFlow::flowPath(source, sink)
 select sink.getNode(), source, sink, "This logging sink is reachable from this $@", sink.getNode(),
   "credential source"
