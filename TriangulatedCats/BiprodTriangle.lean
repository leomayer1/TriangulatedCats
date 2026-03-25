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

def dist_biprodTriangle (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C) :
    BiprodTriangle T T' ∈ distTriang C := by
  obtain ⟨C, g, h, H⟩ := distinguished_cocone_triangle (biprod.map T.mor₁ T'.mor₁)
  obtain ⟨φ, _, _⟩ :=
    complete_distinguished_triangle_morphism _ _ hT H biprod.inl biprod.inl (by aesop)
  obtain ⟨φ', _, _⟩ :=
    complete_distinguished_triangle_morphism _ _ hT' H biprod.inr biprod.inr (by aesop)
  apply isomorphic_distinguished _ H
  let Φ : BiprodTriangle T T' ⟶ Triangle.mk (biprod.map T.mor₁ T'.mor₁) g h :=
    Triangle.homMk _ _ (𝟙 _) (𝟙 _) (biprod.desc φ φ')
  have : IsIso Φ := Triangle.isIso_of_isIsos Φ (IsIso.id _) (IsIso.id _)
    (by
      refine isIso_of_yoneda_map_bijective _ (fun A => ⟨?_, ?_⟩)
      . intro a₁ a₂ ha
        sorry
      . intro a
        sorry
    )
  apply asIso Φ
