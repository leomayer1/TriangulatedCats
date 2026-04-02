import TriangulatedCats.ThickSubcategory

noncomputable section

open CategoryTheory Limits ObjectProperty Functor Pretriangulated

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

def RightComplement (B : Set C) : ThickSubcategory C := sorry
def LeftComplement (A : Set C) : ThickSubcategory C := sorry

theorem exists_SOD_left (ha : IsLeftAdmissible A) : ∃ S : SOD C, A = S.A := sorry
theorem exists_SOD_right (ha : IsRightAdmissible B) : ∃ S : SOD C, B = S.B := sorry

end admissible
