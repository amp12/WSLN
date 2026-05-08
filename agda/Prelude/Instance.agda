module Prelude.Instance where

open import Prelude.Level

----------------------------------------------------------------------
-- Instance
----------------------------------------------------------------------
it : {l : Level} {A : Set l} → {{A}} → A
it {{x}} = x
