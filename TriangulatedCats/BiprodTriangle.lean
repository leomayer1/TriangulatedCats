import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.Triangulated.Basic

open CategoryTheory
open Limits Category Preadditive Pretriangulated ZeroObject

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]

variable {T T' : Triangle C}

local instance (i : ℤ) : PreservesBinaryBiproducts (shiftFunctor C i) :=
  preservesBinaryBiproducts_of_preservesBinaryProducts (shiftFunctor C i)

@[simps!]
noncomputable
def BiprodTriangle (T T' : Triangle C) : Triangle C := Triangle.mk (biprod.map T.mor₁ T'.mor₁)
    (biprod.map T.mor₂ T'.mor₂) (biprod.map T.mor₃ T'.mor₃ ≫ (Functor.mapBiprod _ _ _).inv)


/- A very strange proof: mathlib already has that the product of distinguished triangles
  is distinguished, so I bootstrap that by showing the biprodTriangle is isomorphic
  to a product indexed by WalkingPair. There are some definitional quagmires, but
  this ultimately avoids a longer diagram chase. Ideally there would be
    1) a predicate P on triangles expressing that Hom is (co)homological
    2) a proof that P is closed under sums, products, etc
    3) a proof that the five lemma holds for triangles satisfying P
  -/
theorem dist_biprodTriangle (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C) :
    BiprodTriangle T T' ∈ distTriang C := by
  have H := productTriangle_distinguished (fun j => WalkingPair.casesOn j T T')
    (fun j => WalkingPair.casesOn j hT hT')
  apply isomorphic_distinguished _ H
  apply Triangle.isoMk _ _ ?_ ?_ ?_ ?_ ?_ ?_
  . apply Iso.mk ?_ ?_ (?_) (?_)
    . apply Pi.lift fun j => WalkingPair.casesOn j ?_ ?_
      exact biprod.fst
      exact biprod.snd
    . apply biprod.lift (Pi.π _ WalkingPair.left) (Pi.π _ WalkingPair.right)
    . apply biprod.hom_ext <;> simp [Pi.lift_π]
    . exact Pi.hom_ext _ _ fun b => (by cases b <;> simp [Pi.lift_π])
  . apply Iso.mk ?_ ?_ (?_) (?_)
    . apply Pi.lift fun j => WalkingPair.casesOn j ?_ ?_
      exact biprod.fst
      exact biprod.snd
    . apply biprod.lift (Pi.π _ WalkingPair.left) (Pi.π _ WalkingPair.right)
    . apply biprod.hom_ext <;> simp [Pi.lift_π]
    . exact Pi.hom_ext _ _ fun b => (by cases b <;> simp [Pi.lift_π])
  . apply Iso.mk ?_ ?_ (?_) (?_)
    . apply Pi.lift fun j => WalkingPair.casesOn j ?_ ?_
      exact biprod.fst
      exact biprod.snd
    . apply biprod.lift (Pi.π _ WalkingPair.left) (Pi.π _ WalkingPair.right)
    . apply biprod.hom_ext <;> simp [Pi.lift_π]
    . exact Pi.hom_ext _ _ fun b => (by cases b <;> simp [Pi.lift_π])
  · apply Pi.hom_ext
    intro j
    cases j <;> simp [Pi.map_π, Pi.lift_π, Pi.lift_π_assoc]
  · apply Pi.hom_ext
    intro j
    cases j <;> simp [Pi.map_π, Pi.lift_π, Pi.lift_π_assoc]
  · simp [←assoc]
    apply Pi.hom_ext
    intro j
    cases j <;> apply biprod.hom_ext' <;> simp [Pi.lift_π, ←Functor.map_comp, Pi.lift_π_assoc]
