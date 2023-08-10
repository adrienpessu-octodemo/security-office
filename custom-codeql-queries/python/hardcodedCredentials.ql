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
select dict.getParentNode(), dict.getParent(), sink, "This hardcoded value is $@.", sink,
  "used as credentials"
