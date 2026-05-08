module Prelude.WellFounded where

open import Prelude.Empty using (Ø)
open import Prelude.Level

----------------------------------------------------------------------
-- Recursion over well-founded relations
----------------------------------------------------------------------
module wf {l m : Level}{A : Set l}(R : A → A → Set m) where
  -- Accessibility predicate
  data Acc (x : A) : Set (l ⊔ m) where
    acc : (∀ y → R y x → Acc y) → Acc x

  -- Well-founded relation
  iswf : Set (l ⊔ m)
  iswf = ∀ x → Acc x

  -- Well-founded recursion
  module _
    (w : iswf)
    {n : Level}
    (B : A → Set n)
    (b : ∀ x → (∀ y → R y x → B y) → B x)
    where
    private
      Acc→B : ∀ x → Acc x → B x
      Acc→B x (acc a) = b x (λ y r → Acc→B  y (a y r))

    rec : ∀ x → B x
    rec x = Acc→B x (w x)

  -- Irreflexivity
  irrefl :
    (_ : iswf)
    → ----------------
    ∀ x → R x x → Ø{l}
  irrefl w x p = ¬Accx (w x)
    where
    ¬Accx : Acc x → Ø
    ¬Accx (acc f) = ¬Accx (f x p)
