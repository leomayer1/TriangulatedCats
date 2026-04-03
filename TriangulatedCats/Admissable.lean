import TriangulatedCats.ThickSubcategory
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.CategoryTheory.ObjectProperty.Shift

noncomputable section

open CategoryTheory Limits ObjectProperty Functor Preadditive Pretriangulated ZeroObject

open IsStableUnderShift

section sod

variable (C : Type*) [Category C] [HasZeroObject C] [Preadditive C]
  [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

structure SOD where
A : ThickSubcategory C
B : ThickSubcategory C
hom : ∀ b ∈ B, ∀ a ∈ A, IsZero (b ⟶ a)
prop : ∀ x : C, ∃ b ∈ B, ∃ a ∈ A, ∃ f : b ⟶ x, ∃ g : x ⟶ a, ∃ h : a ⟶ b⟦(1 : ℤ)⟧,
  Triangle.mk f g h ∈ distTriang C

end sod


section admissible

variable {C : Type*} [Category C] [HasZeroObject C] [Preadditive C]
  [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

variable (A B : ThickSubcategory C) (S : SOD C)


/- TODO:
  · left admissible category
  · right admissible category
  · SOD
  · the pieces of an SOD are left/right admissible
  · a left/right admissible subcategory has a semi-orthogonal complement
  · 4/2 : FINISH ALL DEFs and theorem statements
-/

#check IsLeftAdjoint
#check ι

def IsLeftAdmissible := IsLeftAdjoint (ι A.carrier)
def IsRightAdmissible := IsRightAdjoint (ι A.carrier)

theorem IsLeftAdmissible_SOD : IsLeftAdmissible S.A := sorry
theorem IsRightAdmissible_SOD : IsRightAdmissible S.B := sorry

def RightComplement (B : Set C) [IsStableUnderShift B ℤ] : ThickSubcategory C where
  carrier := {c : C | ∀ b ∈ B, ∀ f : b ⟶ c, f = 0}
  zero_mem' b hb f := zero_of_to_zero f
  shift_mem' {i} {a} ha b hb f := by
    rw [←map_eq_zero_iff (shiftFunctor C (-i)), ←IsIso.comp_right_eq_zero _ (shiftShiftNeg _ _).hom]
    apply ha (b⟦-i⟧) (le_shift B _ _ hb)
  iso_mem' {a b ha} φ c hc f := by
    rw [←IsIso.comp_right_eq_zero _ φ.inv]
    apply ha _ hc
  obj₃_mem' {T} hT hT₁ hT₂ b hb f := by
    have H : f ≫ T.mor₃ = 0 := by
      rw [←map_eq_zero_iff (shiftFunctor C (-1 : ℤ)), ←IsIso.comp_right_eq_zero _ (shiftShiftNeg _ _).hom]
      apply hT₁ _ (le_shift B _ _ hb)
    obtain ⟨g, rfl⟩ := Triangle.coyoneda_exact₃ T hT _ H
    rw [(hT₂ b hb g), zero_comp]
  smd_mem' {_ _ h} _ hb _ := zero_of_comp_mono biprod.inl (h _ hb _)

def LeftComplement (A : Set C) [IsStableUnderShift A ℤ] : ThickSubcategory C where
  carrier := {c : C | ∀ a ∈ A, ∀ f : c ⟶ a, f = 0}
  zero_mem' _ _ f := zero_of_from_zero f
  shift_mem' {i} {b} hb a ha f := by
    rw [←map_eq_zero_iff (shiftFunctor C (-i)), ←IsIso.comp_left_eq_zero  (shiftShiftNeg _ _).inv _]
    apply hb (a⟦-i⟧) (le_shift A _ _ ha)
  iso_mem' {a b ha} φ c hc f := by
    rw [←IsIso.comp_left_eq_zero φ.hom _]
    apply ha _ hc
  obj₃_mem' {T} hT hT₁ hT₂ a ha f := by
    obtain ⟨g, rfl⟩ := Triangle.yoneda_exact₃ T hT f (hT₂ _ ha _)
    have hg : g = 0 := by
      rw [←map_eq_zero_iff (shiftFunctor C (-1)), ←IsIso.comp_left_eq_zero  (shiftShiftNeg _ _).inv _]
      apply hT₁ (a⟦-1⟧) (le_shift A _ _ ha)
    rw [hg, comp_zero]
  smd_mem' {_ _ h} _ hb _ := zero_of_epi_comp biprod.fst (h _ hb _)

notation "ᗮ" A => LeftComplement A
notation A "ᗮ" => RightComplement A


theorem exists_SOD_left (ha : IsLeftAdmissible A) : ∃ S : SOD C, A = S.A := sorry
theorem exists_SOD_right (ha : IsRightAdmissible B) : ∃ S : SOD C, B = S.B := sorry

end admissible
