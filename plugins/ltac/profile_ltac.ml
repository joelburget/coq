module M = CString.Map

type treenode = {
  name : M.key;
  total : float;
  local : float;
  ncalls : int;
  max_total : float;
  children : treenode M.t
}
