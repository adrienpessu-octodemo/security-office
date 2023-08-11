/**
* @name Find hardcoded password in setPassword() calls
* @description Find hardcoded password in setPassword() calls
* @kind problem
* @problem.severity recommendation
* @id java/suppresswarnings-pmd
* @tags security
*       maintainability
*       quality
* @precision medium
* @languages java
* 
**/

import java

from MethodAccess ma, Method m
where m = ma.getMethod()
and m.hasName("setPassword")
and ma.getArgument(0).(CompileTimeConstantExpr).getStringValue() != ""
select ma, "Avoid hardcoding passwords when calling setPassword() method "
