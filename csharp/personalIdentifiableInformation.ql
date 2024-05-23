/**
 * @name Find data flows from a personal information source to a logging sink
 * @description Find data flows from a personal information source to a logging sink
 * @id cs/pii-logging
 * @kind path-problem
 * @problem.severity error
 * @security-severity 9.8
 * @precision high
 * @tags security
 *       cwe-359
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
 
 private class PersonalVar extends Assignable {
   pragma[noinline]
   PersonalVar() {
     exists(string name | name = this.getName() |
       name.regexpMatch("(?i).*[mM]obilePhoneNo.*")
 or
       name.regexpMatch("(?i).*[aA]ddressListNewInformation.*")
 or
       name.regexpMatch("(?i).*[cC]ustomerInfo.*")
 or
       name.regexpMatch("(?i).*[cC]VV2.*")
 or
       name.regexpMatch("(?i).*[mM]otherMaidenName.*")
 or
       name.regexpMatch("(?i).*[eE]xpiryDate.*")
 or
       name.regexpMatch("(?i).*[nN]ewPin.*")
 or
       name.regexpMatch("(?i).*[cC]learCardNumber.*")
 or
       name.regexpMatch("(?i).*[aA]silKartNo.*")
 or
       name.regexpMatch("(?i).*[cC]ardRefNumber.*")
 or
       name.regexpMatch("(?i).*[mM]ainCardRefNumber.*")
 or
       name.regexpMatch("(?i).*[cC]artNo.*")
 or
       name.regexpMatch("(?i).*[cC]ellPhoneNumber.*")
 or
       name.regexpMatch("(?i).*[sS]treet.*")
 or
       name.regexpMatch("(?i).*District.*")
 or
       name.regexpMatch("(?i).*[aA]nswer.*")
 or
       name.regexpMatch("(?i).*IBSerialNo.*")
 or
       name.regexpMatch("(?i).*IdentityType.*")
 or
       name.regexpMatch("(?i).*[cC]ardNo.*")
 or
       name.regexpMatch("(?i).*[cC]ardNoLast6Digit.*")
 or
       name.regexpMatch("(?i).*[sS]hadowCardNumber.*")
 or
       name.regexpMatch("(?i).*[cC]ardSerialNo.*")
 or
       name.regexpMatch("(?i).*TCKN.*")
 or
       name.regexpMatch("(?i).*[cC]reditCardNo.*")
 or
       name.regexpMatch("(?i).*PinNo.*")
 or
       name.regexpMatch("(?i).*[cC]ustomersMagicQuestion.*")
 or
       name.regexpMatch("(?i).*[mM]otherName.*")
 or
       name.regexpMatch("(?i).*[fF]atherName.*")
 or
       name.regexpMatch("(?i).*[cC]itizenshipNumber.*")
 or
       name.regexpMatch("(?i).*[aA]ddressDetail.*")
 or
       name.regexpMatch("(?i).*[mM]otherMaidenSurname.*")
 or
       name.regexpMatch("(?i).*[aA]ddresses.*")
 or
       name.regexpMatch("(?i).*[sS]pouseTCKN.*")
 or
       name.regexpMatch("(?i).*TotalIncome.*")
 or
       name.regexpMatch("(?i).*[nN]etSalary.*")
 or
       name.regexpMatch("(?i).*[aA]ddressList.*")
 or
       name.regexpMatch("(?i).*[aA]ddressListNew.*")
 or
       name.regexpMatch("(?i).*[sS]ecurityImageId.*")
 or
       name.regexpMatch("(?i).*DrivingLicenseNo.*")
 or
       name.regexpMatch("(?i).*[cC]itizenNumber.*")
 or
       name.regexpMatch("(?i).*PaymentCreditCardNo.*")
 or
       name.regexpMatch("(?i).*[fF]]irmName.*")
 or
       name.regexpMatch("(?i).*IdentityNo.*")
 or
       name.regexpMatch("(?i).*[rR]eceiverAddress.*")
 or
       name.regexpMatch("(?i).*[pP]ayerAdress.*")
 or
       name.regexpMatch("(?i).*[mM]onthlyIncome.*")
 or
       name.regexpMatch("(?i).*TckNo.*")
 or
       name.regexpMatch("(?i).*[sS]enderAddress.*")
 or
       name.regexpMatch("(?i).*OTP.*")
 or
       name.regexpMatch("(?i).*VERIFICATIONCODE.*")
 or
       name.regexpMatch("(?i).*[sS]ECURITYQUESTION.*")
     )
   }
 }
 
 class CredentialsSource extends DataFlow::Node {
   CredentialsSource() {
     exists(PersonalVar cv | this.asExpr() = cv.getAnAccess())
     or
     exists(Variable v, PersonalVar cv, PropertyAccess pa, VariableAccess va |
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
  
 /* data flow */
 from LoggingFlow::PathNode source, LoggingFlow::PathNode sink
 where LoggingFlow::flowPath(source, sink)
 select sink.getNode(), source, sink, "A personal information has been logged $@", source.getNode(),
   " source"
