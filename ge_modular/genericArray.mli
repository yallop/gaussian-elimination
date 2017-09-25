module Impl (Dom:Domains.S with type 'a exp = 'a code)
  : Container.Cont2D with type 'a rep = 'a Dom.exp
