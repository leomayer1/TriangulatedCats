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
    BiprodTriangle T T' ∈ distTriang C := sorry

/-    by
  have H := productTriangle_distinguished (fun j => WalkingPair.casesOn j T T')
    (fun j => WalkingPair.casesOn j hT hT')
  apply isomorphic_distinguished _ H
  apply Triangle.isoMk _ _ ?_ ?_ ?_ ?_ ?_ ?_
  . apply Iso.mk ?_ ?_ ?_ ?_
    . apply Pi.lift fun j => WalkingPair.casesOn j ?_ ?_
      exact biprod.fst
      exact biprod.snd
    . apply biprod.lift (Pi.π _ WalkingPair.left) (Pi.π _ WalkingPair.right)
    . apply biprod.hom_ext
      . simp
        apply biprod.hom_ext'
        . simp
        . simp
      . simp
    . sorry
  . apply IsLimit.conePointsIsoOfNatIso (BinaryBiproduct.isLimit _ _) (limit.isLimit _)
    symm
    apply diagramIsoPair
  . apply IsLimit.conePointsIsoOfNatIso (BinaryBiproduct.isLimit _ _) (limit.isLimit _)
    symm
    apply diagramIsoPair
  .
  . sorry
  . sorry


  /- apply IsLimit.conePointsIsoOfNatIso (BinaryBiproduct.isLimit _ _) (limit.isLimit _)
    symm
    apply diagramIsoPair
  -/

  /-apply Triangle.isoMk _ _ ?_ ?_ ?_ ?_ ?_ ?_
  . apply Iso.mk ?_ ?_ (?_) (?_)
    . apply Pi.lift fun j => WalkingPair.casesOn j ?_ ?_
      exact biprod.fst
      exact biprod.snd
    . apply biprod.lift (Pi.π _ WalkingPair.left) (Pi.π _ WalkingPair.right)
    . simp
    . simp [productTriangle_obj₁, BiprodTriangle_obj₁]
      ext j
      cases j <;> aesop
  . apply Iso.mk ?_ ?_ (?_) (?_)
    . apply Pi.lift fun j => WalkingPair.casesOn j ?_ ?_
      exact biprod.fst
      exact biprod.snd
    . apply biprod.lift (Pi.π _ WalkingPair.left) (Pi.π _ WalkingPair.right)
    . aesop
    . simp only [productTriangle_obj₂, BiprodTriangle_obj₂]
      ext j
      cases j <;> simp
  . apply Iso.mk ?_ ?_ (?_) (?_)
    . apply Pi.lift fun j => WalkingPair.casesOn j ?_ ?_
      exact biprod.fst
      exact biprod.snd
    . apply biprod.lift (Pi.π _ WalkingPair.left) (Pi.π _ WalkingPair.right)
    . aesop
    . simp only [productTriangle_obj₃, BiprodTriangle_obj₃]
      ext j
      cases j <;> simp
  all_goals
  simp
  ext j <;>
  cases j <;>
  simp [←Functor.map_comp]-/
-/
