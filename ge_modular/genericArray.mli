module Impl (Dom:Domains.S with type 'a exp = 'a code)
  : Container.Cont2D with type 'a rep = 'a Dom.exp

module Impl_static (Dom:Domains.S with type 'a exp = 'a)
  : Container.Cont2D with type 'a rep = 'a Dom.exp
