import TriangulatedCats.ThickSubcategory
import TriangulatedCats.BiprodTriangle
import Mathlib.CategoryTheory.ObjectProperty.Shift
import Mathlib.CategoryTheory.EssentialImage
import Mathlib.Data.ENat.Lattice


open CategoryTheory
open Limits Category Preadditive Pretriangulated ZeroObject ObjectProperty

namespace CategoryTheory.ObjectProperty

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasBinaryBiproducts C] (P : ObjectProperty C)

class IsClosedUnderBiprod where
  of_biprod {a b : C} (ha : P a) (hb : P b) : P (a ⊞ b)

class IsClosedUnderSmd where
  of_smd_left {a b : C} (h : P (a ⊞ b)) : P a
  of_smd_right {a b : C} (h : P (a ⊞ b)) : P b

end ObjectProperty

section defs

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]
variable (I J K : Set C)

inductive addc : Set C
| zero : addc 0
| of_mem' (a : C) : I a → addc a
| of_shift' (i : ℤ) (a : C) : addc a → addc (a⟦i⟧)
| of_iso' (a b : C) : addc a → (a ≅ b) → addc b
| biprod' (a b : C) : addc a → addc b → addc (a ⊞ b)

inductive smd : Set C
| of_mem' (a : C) : I a → smd a
| of_smd_left' (a b : C) : smd (a ⊞ b) → smd a
| of_smd_right' (a b : C) : smd (a ⊞ b) → smd b

def star' : Set C :=
  {c | ∃ a ∈ I, ∃ b ∈ J, ∃ f : a ⟶ c, ∃ g : c ⟶ b, ∃ h : b ⟶ a⟦1⟧, Triangle.mk f g h ∈ distTriang C}

infixl:60 " ⋆ " => star'

abbrev dia : Set C := smd (star' (addc I) (addc J))

infixl:60 " ⋄ " => dia

abbrev level : ℕ → Set C
| 0 => smd (addc {0})
| (n + 1) => level n ⋄ I

notation " ⟪" I "⟫' " n => level I n

def thick_cl' : Set C := ⋃ n : ℕ, level I n

notation " ⟪" I "⟫ " => thick_cl' I

def is_generator (G : C) := ⟪{G}⟫ = ⊤

def is_strong_generator (G : C) := ∃ n : ℕ, (⟪{G}⟫' (n + 1)) = ⊤

noncomputable
def gen_time (G : C) := sInf {n | (⟪{G}⟫' (n + 1)) = ⊤}

noncomputable
def dimension (C : Type*) [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C] :=
  sInf { n : ℕ∞ | ∃ G : C, is_strong_generator G ∧ n = gen_time G}

end defs

section props

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]
variable {I J K : Set C}
variable (n m : ℕ)

theorem star_assoc [IsTriangulated C] : I ⋆ J ⋆ K = I ⋆ (J ⋆ K) := by
  ext c
  constructor
  . rintro ⟨b₁, ⟨a₁, ha₁, a₂, ha₂, f', g', h', H'⟩, b₂, hb₂, f, g, h, H⟩
    obtain ⟨c₂, f'', g'', H''⟩ := distinguished_cocone_triangle (f' ≫ f)
    obtain ⟨O⟩ := IsTriangulated.octahedron_axiom (rfl) H' H H''
    refine ⟨a₁, ha₁, c₂, ⟨a₂, ha₂, b₂, hb₂, _, _, _, O.mem⟩, _, _, _, H''⟩
  /- This proof of the reserve direction gave me nightmares -/
  . rintro ⟨b₁, hb₁, b₂, ⟨a₁, ha₁, a₂, ha₂, f', g', h', H'⟩, f, g, h, H⟩
    obtain ⟨c₂, h'', f'', H''⟩ := distinguished_cocone_triangle (g ≫ g')
    obtain ⟨O⟩ := IsTriangulated.octahedron_axiom (rfl) (rot_of_distTriang _ H) (rot_of_distTriang _ H') (H'')
    refine ⟨c₂⟦-1⟧, ⟨b₁, hb₁, a₁, ha₁, ?_, ?_, f' ≫ h, ?_⟩, a₂, ha₂, _, _, _, inv_rot_of_distTriang _ H''⟩
    . exact -(shiftShiftNeg _ _).inv ≫ (O.m₁⟦-1⟧')
    . exact -(O.m₃⟦-1⟧') ≫ (shiftShiftNeg _ _).hom
    . apply isomorphic_distinguished _ (Triangle.shift_distinguished _ O.mem (-1))
      apply Triangle.isoMk _ _ (shiftShiftNeg b₁ (1 : ℤ)).symm (Iso.refl (c₂⟦-1⟧)) (shiftShiftNeg a₁ (1 : ℤ)).symm
        (comm₁ := sorry)
        (comm₂ := sorry)
        (comm₃ := sorry)

theorem addc.of_mem {a : C} (ha : a ∈ I) : a ∈ addc I := addc.of_mem' a ha
theorem addc.of_shift {i : ℤ} {a : C} (ha : a ∈ addc I) : a⟦i⟧ ∈ addc I := addc.of_shift' i a ha
theorem addc.of_iso {a b : C} (ha : a ∈ addc I) (φ : a ≅ b) : b ∈ addc I := addc.of_iso' a b ha φ
theorem addc.biprod {a b : C} (ha : a ∈ addc I) (hb : b ∈ addc I) : (a ⊞ b) ∈ addc I :=
  addc.biprod' a b ha hb

theorem smd.of_mem {a : C} (ha : a ∈ I) : a ∈ smd I := smd.of_mem' a ha
theorem smd.of_smd_left {a b : C} (hab : (a ⊞ b) ∈ smd I) : a ∈ smd I := smd.of_smd_left' a b hab
theorem smd.of_smd_right {a b : C} (hab : (a ⊞ b) ∈ smd I) : b ∈ smd I := smd.of_smd_right' a b hab

theorem subset_smd : I ⊆ smd I := fun _ hx => smd.of_mem hx
theorem subset_addc : I ⊆ addc I := fun _ hx => addc.of_mem hx

theorem dia.zero : 0 ∈ I ⋄ J :=
  smd.of_mem ⟨0, addc.zero, 0, addc.zero, _, _, _, contractible_distinguished (0 : C)⟩

theorem addc_mono : Monotone (addc (C := C)) := by
  intro I J hIJ a ha
  induction ha with
  | zero => exact addc.zero
  | of_mem' _ ha => exact addc.of_mem (hIJ ha)
  | of_shift' _ _ ha ih => exact addc.of_shift ih
  | of_iso' _ _ ha hab ih => exact addc.of_iso ih hab
  | biprod' _ _ _ _ iha ihb => exact addc.biprod iha ihb

theorem smd_mono : Monotone (smd (C := C)) := by
  intro I J hIJ a ha
  induction ha with
  | of_mem' _ ha => exact smd.of_mem (hIJ ha)
  | of_smd_left' _ _ _ ih => exact smd.of_smd_left ih
  | of_smd_right' _ _ _ ih => exact smd.of_smd_right ih

theorem star_mono {I I' J J' : Set C} (hI : I ≤ I') (hJ : J ≤ J') : I ⋆ J ≤ I' ⋆ J' := by
  rintro X ⟨a, ha, b, hb, f, g, h, H⟩
  exact ⟨a, hI ha, b, hJ hb, f, g, h, H⟩

theorem dia_mono {I I' J J' : Set C} (hI : I ≤ I') (hJ : J ≤ J') : I ⋄ J ≤ I' ⋄ J' :=
  smd_mono (star_mono (addc_mono hI) (addc_mono hJ))

theorem subset_dia_left : I ⊆ I ⋄ J := le_trans (subset_smd) (smd_mono
  (fun x hx => ⟨x, addc.of_mem hx, 0, addc.zero, _, _, _, contractible_distinguished x⟩))

theorem subset_dia_right : J ⊆ I ⋄ J := le_trans (subset_smd) (smd_mono
  (fun x hx => ⟨0, addc.zero, x, addc.of_mem hx, _, _, _, contractible_distinguished₁ x⟩))

theorem star_subset_dia : I ⋆ J ⊆ I ⋄ J := le_trans subset_smd
    (smd_mono (star_mono (subset_addc) (subset_addc)))


theorem level_mono : Monotone (level I) := monotone_nat_of_le_succ (fun _ => subset_dia_left)

theorem level_mono' (h : I ≤ J) (n : ℕ) : (⟪I⟫' n) ≤ ⟪J⟫' n := by
  induction n with
  | zero => rfl
  | succ n ih => exact dia_mono ih h

theorem thick_cl_mono (h : I ≤ J) : ⟪I⟫ ≤ ⟪J⟫ := Set.iUnion_mono (fun _ => level_mono' h _)

open IsClosedUnderIsomorphisms
open IsStableUnderShift
open IsClosedUnderBiprod
open ContainsZero
open IsClosedUnderSmd

instance : ContainsZero (addc I) := ⟨⟨0, isZero_zero _, addc.zero,⟩⟩
instance [ContainsZero I] [IsClosedUnderIsomorphisms I] : ContainsZero (smd I) := by
  obtain ⟨z, hz, hI⟩ := exists_zero (P := I)
  exact ⟨z, hz, smd.of_mem hI⟩

instance [ContainsZero I] [ContainsZero J] : ContainsZero (I ⋆ J) := by
  obtain ⟨a, ha, haI⟩ := exists_zero (P := I)
  obtain ⟨b, hb, hbJ⟩ := exists_zero (P := J)
  refine ⟨a, ha, ⟨a, haI, b, hbJ, (𝟙 a), 0, 0, ?_⟩⟩
  refine isomorphic_distinguished _ (contractible_distinguished a) _ ?_
  exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) hb.isoZero

instance : IsClosedUnderSmd (smd I) := ⟨smd.of_smd_left, smd.of_smd_right⟩

instance : IsClosedUnderIsomorphisms (addc I) := ⟨fun φ ha => addc.of_iso ha φ⟩
instance [IsClosedUnderIsomorphisms I] : IsClosedUnderIsomorphisms (smd I) := by
  refine ⟨fun {X Y} φ ha => ?_⟩
  induction ha generalizing Y with
  | of_mem' _ h => exact smd.of_mem (of_iso (P := I) φ h)
  | of_smd_left' _ _ _ ih => exact smd.of_smd_left (ih (biprod.mapIso φ (Iso.refl _)))
  | of_smd_right' _ _ _ ih => exact smd.of_smd_right (ih (biprod.mapIso (Iso.refl _) φ))

instance : IsStableUnderShift (addc I) ℤ := ⟨fun _ => ⟨fun _ ha => addc.of_shift ha⟩⟩
instance [IsClosedUnderIsomorphisms I] [IsStableUnderShift I ℤ] : IsStableUnderShift (smd I) ℤ := by
  refine ⟨fun i => ⟨fun a ha => ?_⟩⟩
  have := preservesBinaryBiproducts_of_preservesBinaryProducts (shiftFunctor C i)
  induction ha with
  | of_mem' _ h => exact smd.of_mem (le_shift (P := I) _ _ h)
  | of_smd_left' _ _ _ ih =>
    apply smd.of_smd_left
    apply (of_iso (Functor.mapBiprod _ _ _) ih)
  | of_smd_right' _ _ _ ih =>
    apply smd.of_smd_right
    apply (of_iso (Functor.mapBiprod _ _ _) ih)

instance : IsClosedUnderIsomorphisms (I ⋆ J) := ⟨by
  rintro c c' φ ⟨a, ha, b, hb, f, g, h, H⟩
  refine ⟨a, ha, b, hb, f ≫ φ.hom, φ.inv ≫ g, h, ?_⟩
  exact isomorphic_distinguished _ H _ (Triangle.isoMk _ _ (Iso.refl a) φ.symm (Iso.refl b))⟩

instance [IsStableUnderShift I ℤ] [IsStableUnderShift J ℤ] : IsStableUnderShift (I ⋆ J) ℤ :=
  ⟨fun i => ⟨by
    rintro c ⟨a, ha, b, hb, f, g, h, H⟩
    refine ⟨a⟦i⟧, ?_, b⟦i⟧, ?_, _, _, _, Triangle.shift_distinguished _ H i⟩
    exact le_shift I i a ha
    exact le_shift J i b hb⟩⟩

instance : IsClosedUnderBiprod (addc I) := ⟨addc.biprod⟩
instance [IsClosedUnderBiprod I] [IsClosedUnderIsomorphisms I] : IsClosedUnderBiprod (smd I) := ⟨fun ha hb => by
  induction ha with
  | of_mem' a ha =>
    induction hb with
    | of_mem' b hb => exact smd.of_mem (of_biprod (P := I) ha hb)
    | of_smd_left' b b' hb ih =>
      apply smd.of_smd_left (b := b') (of_iso (P := smd I) (biprod.associator a b b').symm ih)
    | of_smd_right' b b' hb ih =>
      apply smd.of_smd_right (a := b) (of_iso (P := smd I) ?_ ih)
      exact (biprod.associator a b b').symm ≪≫
        biprod.mapIso (biprod.braiding _ _) (Iso.refl _) ≪≫ biprod.associator b a b'
  | of_smd_left' a a' ha ih =>
    apply smd.of_smd_right (a := a') (of_iso (P := smd I) ?_ ih)
    exact biprod.mapIso (biprod.braiding _ _) (Iso.refl _) ≪≫ biprod.associator _ _ _
  | of_smd_right' a a' hb ih =>
    apply smd.of_smd_right (a := a) (of_iso (P := smd I) (biprod.associator _ _ _) ih)⟩

instance [IsClosedUnderBiprod I] [IsClosedUnderBiprod J] : IsClosedUnderBiprod (I ⋆ J) := by
  constructor
  rintro c c' ⟨a, ha, b, hb, f, g, h, H⟩ ⟨a', ha', b', hb', f', g', h', H'⟩
  refine ⟨_, ?_, _, ?_, _, _, _, dist_biprodTriangle H H'⟩
  apply of_biprod (P := I) ha ha'
  apply of_biprod (P := J) hb hb'

@[simp]
theorem addc_eq_self [ContainsZero I] [IsClosedUnderIsomorphisms I] [IsStableUnderShift I ℤ]
    [IsClosedUnderBiprod I] : addc I = I := by
  refine le_antisymm (fun a ha => ?_) subset_addc
  induction ha with
  | zero => exact prop_zero (P := I)
  | of_mem' _ ha => exact ha
  | of_shift' _ _ _ ih => exact le_shift (P := I) _ _ ih
  | of_iso' a b _ φ ih => exact of_iso (P := I) φ ih
  | biprod' a b _ _ iha ihb => exact of_biprod (P := I) iha ihb

@[simp]
theorem smd_smd_star : smd (smd I ⋆ J) = smd (I ⋆ J) := by
  have := preservesBinaryBiproducts_of_preservesBinaryProducts (shiftFunctor C (1 : ℤ))
  apply le_antisymm (fun c hc => ?_) (smd_mono (star_mono subset_smd le_rfl))
  induction hc with
  | of_mem' c hc =>
    obtain ⟨a, ha, b, hb, f, g, h, H⟩ := hc
    induction ha generalizing c with
    | of_mem' a ha => exact smd.of_mem ⟨a, ha, b, hb, f, g, h, H⟩
    | of_smd_left' a a' _ ih =>
      apply smd.of_smd_left
      apply ih (c ⊞ a') (biprod.map f (𝟙 a')) (biprod.desc g 0)
          (biprod.lift h 0 ≫ (Functor.mapBiprod _ _ _).inv)
      apply isomorphic_distinguished _ (dist_biprodTriangle H (contractible_distinguished a'))
      apply Triangle.isoMk _ _ (Iso.refl (a ⊞ a')) (Iso.refl (c ⊞ a')) (isoBiprodZero (isZero_zero _))
    | of_smd_right' a' a _ ih =>
      apply smd.of_smd_right
      apply ih (a' ⊞ c) (biprod.map (𝟙 a') f) (biprod.desc 0 g)
          (biprod.lift 0 h ≫ (Functor.mapBiprod _ _ _).inv)
      apply isomorphic_distinguished _ (dist_biprodTriangle (contractible_distinguished a') H)
      apply Triangle.isoMk _ _ (Iso.refl (a' ⊞ a)) (Iso.refl (a' ⊞ c)) (isoZeroBiprod (isZero_zero _))
  | of_smd_left' _ _ _ ih => exact smd.of_smd_left ih
  | of_smd_right' _ _ _ ih => exact smd.of_smd_right ih

@[simp]
theorem smd_star_smd : smd (I ⋆ smd J) = smd (I ⋆ J) := by
  have := preservesBinaryBiproducts_of_preservesBinaryProducts (shiftFunctor C (1 : ℤ))
  apply le_antisymm (fun c hc => ?_) (smd_mono (star_mono le_rfl subset_smd))
  induction hc with
  | of_mem' c hc =>
    obtain ⟨a, ha, b, hb, f, g, h, H⟩ := hc
    induction hb generalizing c with
    | of_mem' b hb => exact smd.of_mem ⟨a, ha, b, hb, f, g, h, H⟩
    | of_smd_left' b b' _ ih =>
      apply smd.of_smd_left
      apply ih (c ⊞ b') (biprod.lift f 0) (biprod.map g (𝟙 b')) (biprod.desc h 0)
      apply isomorphic_distinguished _ (dist_biprodTriangle H (contractible_distinguished₁ b'))
      apply Triangle.isoMk _ _ (isoBiprodZero (isZero_zero _)) (Iso.refl (c ⊞ b')) (Iso.refl (b ⊞ b'))
    | of_smd_right' b' b _ ih =>
      apply smd.of_smd_right
      apply ih (b' ⊞ c) (biprod.lift 0 f) (biprod.map (𝟙 _) g) (biprod.desc 0 h)
      apply isomorphic_distinguished _ (dist_biprodTriangle (contractible_distinguished₁ b') H)
      apply Triangle.isoMk _ _ (isoZeroBiprod (isZero_zero _)) (Iso.refl (b' ⊞ c)) (Iso.refl (b' ⊞ b))
  | of_smd_left' _ _ _ ih => exact smd.of_smd_left ih
  | of_smd_right' _ _ _ ih => exact smd.of_smd_right ih

@[simp]
theorem smd_smd : smd (smd I) = smd I := by
  apply le_antisymm (fun a ha => ?_) subset_smd
  induction ha with
  | of_mem' a ha => exact ha
  | of_smd_left' _ _ _ ih => exact smd.of_smd_left ih
  | of_smd_right' _ _ _ ih => exact smd.of_smd_right ih

theorem star_eq₂ : I ⋆ J = {c | ∃ a ∈ I, ∃ b ∈ J, ∃ f : a ⟶ c, ∃ g : c ⟶ b, ∃ h : b ⟶ a⟦1⟧,
    Triangle.mk f g h ∈ distTriang C} := rfl

theorem star_eq₁ [IsStableUnderShift I ℤ] : I ⋆ J = {c | ∃ b ∈ J, ∃ a ∈ I,
    ∃ f : c ⟶ b, ∃ g : b ⟶ a, ∃ h : a ⟶ c⟦1⟧, Triangle.mk f g h ∈ distTriang C} := by
  ext
  constructor
  . rintro ⟨a, ha, b, hb, f, g, h, H⟩
    exact ⟨b, hb, a⟦(1 : ℤ)⟧, le_shift I _ _ ha, _, _, _, rot_of_distTriang _ H⟩
  . rintro ⟨b, hb, a, ha, f, g, h, H⟩
    exact ⟨a⟦-1⟧, le_shift I _ _ ha, b, hb, _, _, _, inv_rot_of_distTriang _ H⟩

theorem star_eq₃ [IsStableUnderShift J ℤ] : I ⋆ J = {c | ∃ b ∈ J, ∃ a ∈ I,
    ∃ f : b ⟶ a, ∃ g : a ⟶ c, ∃ h : c ⟶ b⟦1⟧, Triangle.mk f g h ∈ distTriang C} := by
  ext
  constructor
  . rintro ⟨a, ha, b, hb, f, g, h, H⟩
    exact ⟨b⟦-1⟧, le_shift J _ _ hb, a, ha, _, _, _, inv_rot_of_distTriang _ H⟩
  . rintro ⟨b, hb, a, ha, f, g, h, H⟩
    exact ⟨a, ha, b⟦(1 : ℤ)⟧, le_shift J _ _ hb, _, _, _, rot_of_distTriang _ H⟩

theorem level_of_smd_left {a b : C} (hab : (a ⊞ b) ∈ (⟪I⟫' n)) : a ∈ ⟪I⟫' n := by
  cases n <;> exact smd.of_smd_left hab
theorem level_of_smd_right {a b : C} (hab : (a ⊞ b) ∈ (⟪I⟫' n)) : b ∈ ⟪I⟫' n := by
  cases n <;> exact smd.of_smd_right hab

instance : ContainsZero (⟪I⟫' n) := by cases n <;> infer_instance
instance : IsClosedUnderIsomorphisms (⟪I⟫' n) := by cases n <;> infer_instance
instance : IsStableUnderShift (⟪I⟫' n) ℤ := by cases n <;> infer_instance
instance : IsClosedUnderBiprod (⟪I⟫' n) := by cases n <;> infer_instance
instance : IsClosedUnderSmd (⟪I⟫' n) := by cases n <;> infer_instance

instance : ContainsZero ⟪I⟫ := ⟨⟨0, isZero_zero _, ⟨_, ⟨0, rfl⟩, smd.of_mem (addc.of_mem rfl)⟩⟩⟩
instance : IsClosedUnderIsomorphisms ⟪I⟫ :=
  ⟨fun φ ⟨_, ⟨n, rfl⟩, ha⟩ => ⟨_, ⟨n, rfl⟩, of_iso (P := ⟪I⟫' n) φ ha⟩⟩
instance : IsStableUnderShift ⟪I⟫ ℤ :=
  ⟨fun _ => ⟨fun _ => fun ⟨_, ⟨n, rfl⟩, ha⟩ => ⟨_, ⟨n, rfl⟩, le_shift (⟪I⟫' n) _ _ ha⟩⟩⟩
instance : IsClosedUnderBiprod ⟪I⟫ :=
  ⟨fun ⟨_, ⟨n, rfl⟩, ha⟩ ⟨_, ⟨m, rfl⟩, hb⟩ => ⟨_, ⟨n + m, rfl⟩, of_biprod (P := ⟪I⟫' n + m)
    (level_mono (Nat.le_add_right _ _) ha)
    (level_mono (Nat.le_add_left _ _) hb)
  ⟩⟩
instance : IsClosedUnderSmd ⟪I⟫ :=
  ⟨fun ⟨_, ⟨n, rfl⟩, h⟩ => ⟨_, ⟨n, rfl⟩, of_smd_left (P := ⟪_⟫' n) h⟩,
   fun ⟨_, ⟨n, rfl⟩, h⟩ => ⟨_, ⟨n, rfl⟩, of_smd_right (P := ⟪_⟫' n) h⟩⟩

theorem addc_isZero : addc IsZero (C := C) = IsZero := by
  apply le_antisymm (fun a ha => ?_) subset_addc
  induction ha with
  | zero => exact isZero_zero _
  | of_mem' _ ha => exact ha
  | of_shift' _ _ ha ih => exact Functor.map_isZero _ ih
  | of_iso' _ _ ha φ ih => apply IsZero.of_iso ih φ.symm
  | biprod' _ _ _ _ iha ihb => exact (biprod_isZero_iff _ _).mpr ⟨iha, ihb⟩

theorem smd_isZero : smd IsZero (C := C) = IsZero := by
  apply le_antisymm (fun a ha => ?_) subset_smd
  induction ha with
  | of_mem' _ ha => exact ha
  | of_smd_left' _ _ _ ih => exact ((biprod_isZero_iff _ _).mp ih).left
  | of_smd_right' _ _ _ ih => exact ((biprod_isZero_iff _ _).mp ih).right

theorem star_isZero [IsClosedUnderIsomorphisms I] : I ⋆ IsZero = I := by
  apply le_antisymm ?_ ?_
  . rintro c ⟨a, ha, b, hb, f, g, h, H⟩
    have : IsIso f := (Triangle.isZero₃_iff_isIso₁ _ H).mp hb
    apply of_iso (P := I) (asIso f) ha
  . exact fun x hx => ⟨x, hx, 0, isZero_zero _, _, _, _, contractible_distinguished _⟩

theorem isZero_star [IsClosedUnderIsomorphisms I] : IsZero ⋆ I = I := by
  apply le_antisymm ?_ ?_
  . rintro c ⟨a, ha, b, hb, f, g, h, H⟩
    have : IsIso g := (Triangle.isZero₁_iff_isIso₂ _ H).mp ha
    refine of_iso (P := I) (asIso g).symm hb
  . refine fun x hx => ⟨0, isZero_zero _, x, hx, _, _, _, contractible_distinguished₁ _⟩

@[simp]
theorem level_zero : (⟪I⟫' 0) = IsZero := by
  apply le_antisymm ?_ ?_
  . rw [←smd_isZero,←addc_isZero]
    apply smd_mono (addc_mono ?_)
    rintro _ rfl
    exact isZero_zero _
  . exact fun a ha => of_iso (P := ⟪I⟫' 0) ha.isoZero.symm (smd.of_mem (addc.of_mem rfl))

@[simp]
theorem level_one : (⟪I⟫' 1) = smd (addc I) := by
  rw [level, level_zero, dia, addc_isZero, isZero_star]

variable [IsTriangulated C]

theorem dia_assoc : I ⋄ J ⋄ K = I ⋄ (J ⋄ K) := by
  rw [dia, dia, dia, dia, addc_eq_self, smd_smd_star, addc_eq_self (I := smd _),
    smd_star_smd, star_assoc]

theorem level_dia_level : (⟪I⟫' n) ⋄ (⟪I⟫' m) = ⟪I⟫' (n + m) := by
  induction m with
  | zero =>
    apply le_antisymm (le_trans (dia_mono le_rfl (le_of_eq level_zero)) ?_) subset_dia_left
    rw [dia, addc_eq_self, addc_isZero, star_isZero]
    cases n <;> rw [smd_smd]
  | succ m ih => rw [level, ←dia_assoc, ih, ←add_assoc]

theorem level_level : level (level I n) m = level I (n * m) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [level, ih, level_dia_level, mul_add, mul_one]

def ThickSubcategory.thick_cl (I : Set C) : ThickSubcategory C where
  carrier := thick_cl' I
  zero_mem' := ⟨_, ⟨0, rfl⟩, smd.of_mem (addc.of_mem rfl)⟩
  shift_mem' {i a} ha := le_shift ⟪I⟫ i a ha
  iso_mem' {a b} ha φ := of_iso (P := ⟪I⟫) φ ha
  obj₃_mem' hT := fun ⟨_, ⟨n, rfl⟩, h₁⟩ ⟨_, ⟨m, rfl⟩, h₂⟩ => by
    refine ⟨_, ⟨m + n, rfl⟩, ?_⟩
    show _ ∈ ⟪I⟫' (m + n)
    rw [←level_dia_level]
    apply star_subset_dia
    rw [star_eq₃]
    exact ⟨_, h₁, _, h₂, _, _, _, hT⟩
  smd_mem' {a b} hab := of_smd_left (P := ⟪I⟫) hab


end props

namespace Functor

variable {C D : Type*} [Category C] [Category D] [Preadditive D]
  [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]
variable {F : C ⥤ D}
variable (I J : Set C)
variable (K : Set D)
variable {G : C}

/- A functor `F : C ⥤ D` is dense if any object `d : D` is a summand of an object in the
image of `F` -/
def Dense := smd (essImage F) = ⊤

open IsClosedUnderIsomorphisms IsClosedUnderSmd

theorem eq_top_of_contains_of_dense (hF : F.Dense) {I : Set D} [IsClosedUnderIsomorphisms I]
  [IsClosedUnderSmd I] (hI : F.obj '' ⊤ ⊆ I) : I = ⊤ := by
    apply le_antisymm le_top
    rw [←hF]
    intro d hd
    induction hd with
    | of_mem' _ ha =>
      obtain ⟨c, ⟨φ⟩⟩ := ha
      apply of_iso (P := I) φ (hI ⟨c, trivial, rfl⟩)
    | of_smd_left' _ _ _ ih => exact of_smd_left (P := I) ih
    | of_smd_right' _ _ _ ih => exact of_smd_right (P := I) ih

variable [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]
  [F.CommShift ℤ] [F.IsTriangulated]

theorem functor_addc : F.obj '' (addc I) ⊆ addc (F.obj '' I) := by
  rintro _ ⟨c, hc, rfl⟩
  induction hc with
  | zero => exact addc.of_iso addc.zero (IsZero.isoZero (F.map_isZero (isZero_zero _))).symm
  | of_mem' a ha => exact addc.of_mem ⟨a, ha, rfl⟩
  | of_shift' _ _ _ ih => exact addc.of_iso (addc.of_shift ih) ((F.commShiftIso _).app _).symm
  | of_iso' _ _ _ φ ih => exact addc.of_iso ih (F.mapIso φ)
  | biprod' _ _ _ _ iha ihb =>
    apply addc.of_iso (addc.biprod iha ihb) --
    have := preservesBinaryBiproducts_of_preservesBinaryProducts F
    apply (F.mapBiprod _ _).symm

theorem functor_smd [IsClosedUnderIsomorphisms K] (h : F.obj '' I ⊆ K) :
    F.obj '' (smd I) ⊆ smd K := by
  rintro _ ⟨c, hc, rfl⟩
  have := preservesBinaryBiproducts_of_preservesBinaryProducts F
  induction hc with
  | of_mem' _ hc => exact smd.of_mem (h ⟨_, hc, rfl⟩)
  | of_smd_left' _ _ _ ih => exact smd.of_smd_left (of_iso (P := smd K) (F.mapBiprod _ _) ih)
  | of_smd_right' _ _ _ ih => exact smd.of_smd_right (of_iso (P := smd K) (F.mapBiprod _ _) ih)

theorem functor_star : F.obj '' (I ⋆ J) ⊆ (F.obj '' I) ⋆ (F.obj '' J) := by
  rintro _ ⟨b, ⟨a, ha, c, hc, f, g, h, H⟩, rfl⟩
  refine ⟨_, ⟨a, ha, rfl⟩, _, ⟨c, hc, rfl⟩, _, _, _, F.map_distinguished _ H⟩

theorem functor_dia : F.obj '' (I ⋄ J) ⊆ (F.obj '' I) ⋄ (F.obj '' J) :=
  functor_smd _ _ (le_trans (functor_star _ _) (star_mono (functor_addc I) (functor_addc J)))

theorem functor_level {n : ℕ} : F.obj '' (⟪I⟫' n) ⊆ ⟪F.obj '' I⟫' n := by
  induction n with
  | zero =>
    rintro _ ⟨c, hc, rfl⟩
    rw [level_zero] at hc ⊢
    apply map_isZero F hc
  | succ n ih => exact le_trans (functor_dia _ _) (dia_mono ih le_rfl)

theorem functor_thick_cl' : F.obj '' ⟪I⟫ ⊆ ⟪F.obj '' I⟫ := by
  rw [thick_cl', Set.image_iUnion]
  apply Set.iUnion_mono (fun n => functor_level _)

theorem functor_is_generator
  (hF : F.Dense) (hG : is_generator G) : is_generator (F.obj G) := by
  apply eq_top_of_contains_of_dense hF
  rw [←hG, ←Set.image_singleton]
  apply functor_thick_cl'

theorem functor_is_strong_generator (hF : F.Dense) (hG : is_strong_generator G) : is_strong_generator (F.obj G) := by
  obtain ⟨n, hn⟩ := hG
  use n
  apply eq_top_of_contains_of_dense hF
  rw [←hn, ←Set.image_singleton]
  apply functor_level

theorem level_gen_time (hG : is_strong_generator G) : (⟪{G}⟫' (gen_time G + 1)) = ⊤ := by
  obtain ⟨n, hn⟩ := hG
  exact Nat.sInf_mem (s := {n | (⟪{G}⟫' (n + 1)) = ⊤}) ⟨n, hn⟩

theorem gen_time_le {n : ℕ} (hG : (⟪{G}⟫' (n + 1)) = ⊤) : gen_time G ≤ n := Nat.sInf_le hG

theorem dim_le_gen_time (hG : is_strong_generator G) : dimension C ≤ gen_time G := sInf_le ⟨G, hG, rfl⟩

theorem exists_gen_of_dim_eq_cast {n : ℕ} (h : dimension C = n) :
    ∃ G : C, is_strong_generator G ∧ gen_time G = dimension C := by
  have H : dimension C < n + 1 := by
    rw [h]
    norm_cast
    norm_num
  rw [dimension, sInf_lt_iff] at H
  obtain ⟨_, ⟨G, hG, rfl⟩, hn⟩ := H
  refine ⟨G, hG, ?_⟩
  apply le_antisymm _ (dim_le_gen_time hG)
  rw [h]
  norm_cast at *
  rw [←Nat.lt_succ_iff]
  exact hn

theorem functor_gen_time (hF : F.Dense) (hG : is_strong_generator G) : gen_time (F.obj G) ≤ gen_time G := by
  apply gen_time_le
  apply eq_top_of_contains_of_dense hF
  rw [←level_gen_time hG, ←Set.image_singleton]
  apply functor_level

theorem dim_le_of_dense' (hF : F.Dense) {n : ℕ∞} (hn : dimension C = n) : dimension D ≤ n := by
  cases n with
  | top => exact le_top
  | coe n =>
    obtain ⟨G, hG, h⟩ := exists_gen_of_dim_eq_cast hn
    have H : (gen_time (F.obj G) : ℕ∞) ≤ n := by
      rw [←hn, ←h]
      apply Nat.mono_cast (functor_gen_time hF hG)
    apply le_trans (dim_le_gen_time (functor_is_strong_generator hF hG)) H

theorem dim_le_of_dense (hF : F.Dense) : dimension D ≤ dimension C := dim_le_of_dense' hF rfl

end Functor
