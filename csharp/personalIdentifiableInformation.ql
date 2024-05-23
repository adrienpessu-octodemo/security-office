/**
 * @name Find data flows from a credential source to a logging sink
 * @description Find data flows from a credential source to a logging sink
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
       name.regexpMatch("(?i).*(MobilePhoneNo).*")
 or
       name.regexpMatch("(?i).*(AddressListNewInformation).*")
 or
       name.regexpMatch("(?i).*(CustomerInfo).*")
 or
       name.regexpMatch("(?i).*(CVV2).*")
 or
       name.regexpMatch("(?i).*(MotherMaidenName).*")
 or
       name.regexpMatch("(?i).*(ExpiryDate).*")
 or
       name.regexpMatch("(?i).*(NewPin).*")
 or
       name.regexpMatch("(?i).*(ClearCardNumber).*")
 or
       name.regexpMatch("(?i).*(Password).*")
 or
       name.regexpMatch("(?i).*(AsilKartNo).*")
 or
       name.regexpMatch("(?i).*(CardRefNumber).*")
 or
       name.regexpMatch("(?i).*(MainCardRefNumber).*")
 or
       name.regexpMatch("(?i).*(CartNo).*")
 or
       name.regexpMatch("(?i).*(CellPhoneNumber).*")
 or
       name.regexpMatch("(?i).*(Street).*")
 or
       name.regexpMatch("(?i).*(District).*")
 or
       name.regexpMatch("(?i).*(Answer).*")
 or
       name.regexpMatch("(?i).*(IBSerialNo).*")
 or
       name.regexpMatch("(?i).*(IdentityType).*")
 or
       name.regexpMatch("(?i).*(CardNo).*")
 or
       name.regexpMatch("(?i).*(CardNoLast6Digit).*")
 or
       name.regexpMatch("(?i).*(ShadowCardNumber).*")
 or
       name.regexpMatch("(?i).*(CardSerialNo).*")
 or
       name.regexpMatch("(?i).*(TCKN).*")
 or
       name.regexpMatch("(?i).*(CreditCardNo).*")
 or
       name.regexpMatch("(?i).*(PinNo).*")
 or
       name.regexpMatch("(?i).*(CustomersMagicQuestion).*")
 or
       name.regexpMatch("(?i).*(MotherName).*")
 or
       name.regexpMatch("(?i).*(FatherName).*")
 or
       name.regexpMatch("(?i).*(CitizenshipNumber).*")
 or
       name.regexpMatch("(?i).*(AddressDetail).*")
 or
       name.regexpMatch("(?i).*(MotherMaidenSurname).*")
 or
       name.regexpMatch("(?i).*(Addresses).*")
 or
       name.regexpMatch("(?i).*(SpouseTCKN).*")
 or
       name.regexpMatch("(?i).*(TotalIncome).*")
 or
       name.regexpMatch("(?i).*(NetSalary).*")
 or
       name.regexpMatch("(?i).*(AddressList).*")
 or
       name.regexpMatch("(?i).*(AddressListNew).*")
 or
       name.regexpMatch("(?i).*(SecurityImageId).*")
 or
       name.regexpMatch("(?i).*(DrivingLicenseNo).*")
 or
       name.regexpMatch("(?i).*(CitizenNumber).*")
 or
       name.regexpMatch("(?i).*(PaymentCreditCardNo).*")
 or
       name.regexpMatch("(?i).*(FirmName).*")
 or
       name.regexpMatch("(?i).*(IdentityNo).*")
 or
       name.regexpMatch("(?i).*(ReceiverAddress).*")
 or
       name.regexpMatch("(?i).*(PayerAdress).*")
 or
       name.regexpMatch("(?i).*(MonthlyIncome).*")
 or
       name.regexpMatch("(?i).*(TckNo).*")
 or
       name.regexpMatch("(?i).*(SenderAddress).*")
 or
       name.regexpMatch("(?i).*(OTP).*")
 or
       name.regexpMatch("(?i).*(VERIFICATIONCODE).*")
 or
       name.regexpMatch("(?i).*(SECURITYQUESTION).*")
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
 select sink.getNode(), source, sink, "A personal information has been logged $@", sink.getNode(),
   " source"
