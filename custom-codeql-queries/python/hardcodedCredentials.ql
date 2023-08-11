/**
 * @name Hard-coded credentials
 * @description Credentials are hard coded in the source code of the application.
 * @kind path-problem
 * @problem.severity error
 * @security-severity 9.8
 * @precision medium
 * @id py/hardcoded-credentials-custom
 * @tags security
 *       external/cwe/cwe-259
 *       external/cwe/cwe-321
 *       external/cwe/cwe-798
 */

import python
import semmle.python.Concepts
import semmle.python.ApiGraphs

from Dict dict, Expr sink
where
  exists(KeyValuePair item |
    item = dict.getAnItem() and
    item.getKey().(StrConst).getText().regexpMatch("^(?:client_secret)$")
  |
    sink = item.getValue()
  )
select sink, "This hardcoded value has been used as credentials"
