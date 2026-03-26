import TriangulatedCats.ThickSubcategory
import TriangulatedCats.BiprodTriangle
import Mathlib.CategoryTheory.ObjectProperty.Shift


open CategoryTheory
open Limits Category Preadditive Pretriangulated ZeroObject ObjectProperty

namespace CategoryTheory.ObjectProperty

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasBinaryBiproducts C] (P : ObjectProperty C)

class IsClosedUnderBiprod where
  of_biprod {a b : C} (ha : P a) (hb : P b) : P (a ⊞ b)

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
        (comm₃ := by
          simp
          show f' ≫ h ≫ ((shiftFunctorCompIsoId C 1 (-1) _).inv.app b₁)⟦(1 : ℤ)⟧' =
            (shiftFunctorCompIsoId C 1 (-1) _).inv.app a₁ ≫ f'⟦(1:ℤ)⟧'⟦-1⟧' ≫ h⟦(1 : ℤ)⟧'⟦-1⟧' ≫
            (shiftFunctorComm C 1 (-1)).hom.app (b₁⟦1⟧)
          have HH (hh) (hh'): ((shiftFunctorCompIsoId C 1 (-1) hh).inv.app b₁)⟦(1 : ℤ)⟧' =
            (shiftFunctorCompIsoId C 1 (-1) hh').inv.app (b₁⟦(1 : ℤ)⟧) ≫ (shiftFunctorComm C 1 (-1)).hom.app (b₁⟦1⟧) := by
              rw [shift_shiftFunctorCompIsoId_inv_app]
              simp [shiftFunctorCompIsoId, shiftFunctorComm]
              rw [←assoc]
              convert (id_comp _).symm
              rw [←NatTrans.comp_app, ← shiftFunctorAdd'_eq_shiftFunctorAdd]
              simp
          rw [HH (add_neg_cancel _) (add_neg_cancel _),←assoc,←assoc,←assoc,←assoc]
          congr 1
          nth_rewrite 2 [assoc]
          rw [←Functor.map_comp, ←Functor.map_comp]
          apply NatTrans.naturality (shiftFunctorCompIsoId C 1 (-1) _).inv
        )

abbrev dia : Set C := smd (star' (addc I) (addc J))

infixl:60 " ⋄ " => dia

abbrev level : ℕ → Set C
| 0 => smd (addc {0})
| (n + 1) => level n ⋄ I

notation " ⟪" I "⟫' " n => level I n

def thick_cl' : Set C := ⋃ n : ℕ, level I n

notation " ⟪" I "⟫ " => thick_cl' I

def is_generator (G : C) := ⟪{G}⟫ = ⊤

def is_strong_generator (G : C) := ∃ (n : ℕ), (⟪{G}⟫' n) = ⊤

end defs

section props

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]
variable {I J K : Set C}
variable (n m : ℕ)

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

instance : ContainsZero (⟪I⟫' n) := by cases n <;> infer_instance
instance : IsClosedUnderIsomorphisms (⟪I⟫' n) := by cases n <;> infer_instance
instance : IsStableUnderShift (⟪I⟫' n) ℤ := by cases n <;> infer_instance
instance : IsClosedUnderBiprod (⟪I⟫' n) := by cases n <;> infer_instance

theorem addc_isZero : addc IsZero (C := C) = IsZero := by
  refine le_antisymm (fun a ha => ?_) subset_addc
  induction ha with
  | zero => exact isZero_zero _
  | of_mem' _ ha => exact ha
  | of_shift' _ _ ha ih => exact Functor.map_isZero _ ih
  | of_iso' _ _ ha φ ih => apply IsZero.of_iso ih φ.symm
  | biprod' _ _ _ _ iha ihb => exact (biprod_isZero_iff _ _).mpr ⟨iha, ihb⟩

theorem smd_isZero : smd IsZero (C := C) = IsZero := by
  refine le_antisymm (fun a ha => ?_) subset_smd
  induction ha with
  | of_mem' _ ha => exact ha
  | of_smd_left' _ _ _ ih => exact ((biprod_isZero_iff _ _).mp ih).left
  | of_smd_right' _ _ _ ih => exact ((biprod_isZero_iff _ _).mp ih).right

theorem star_isZero [IsClosedUnderIsomorphisms I] [IsStableUnderShift I ℤ] : I ⋆ IsZero = I := by
  refine le_antisymm ?_ ?_
  . rintro c ⟨a, ha, b, hb, f, g, h, H⟩
    have : IsIso f := (Triangle.isZero₃_iff_isIso₁ _ H).mp hb
    apply of_iso (P := I) (asIso f) ha
  . exact fun x hx => ⟨x, hx, 0, isZero_zero _, _, _, _, contractible_distinguished _⟩

theorem isZero_star [IsClosedUnderIsomorphisms I] [IsStableUnderShift I ℤ] : IsZero ⋆ I = I := by
  refine le_antisymm ?_ ?_
  . rintro c ⟨a, ha, b, hb, f, g, h, H⟩
    have : IsIso g := (Triangle.isZero₁_iff_isIso₂ _ H).mp ha
    refine of_iso (P := I) (asIso g).symm hb
  . refine fun x hx => ⟨0, isZero_zero _, x, hx, _, _, _, contractible_distinguished₁ _⟩

variable [IsTriangulated C]

theorem dia_assoc : I ⋄ J ⋄ K = I ⋄ (J ⋄ K) := by
  rw [dia, dia, dia, dia, addc_eq_self, smd_smd_star, addc_eq_self (I := smd _),
    smd_star_smd, star_assoc]

theorem level_dia_level : (⟪I⟫' n) ⋄ (⟪I⟫' m) = ⟪I⟫' (n + m) := by
  induction m with
  | zero =>
    apply le_antisymm (le_trans (dia_mono le_rfl ?_) ?_) subset_dia_left
    show smd (addc {0}) ≤ IsZero
    . rw [←smd_isZero,←addc_isZero]
      apply smd_mono (addc_mono ?_)
      rintro _ rfl
      exact isZero_zero _
    . rw [dia, addc_eq_self, addc_isZero, star_isZero]
      intro a ha
      cases n <;> rwa [level, smd_smd] at ha
  | succ m ih => rw [level, ←dia_assoc, ih, ←add_assoc]

theorem level_level : level (level I n) m = level I (n * m) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [level, ih, level_dia_level, mul_add, mul_one]

def ThickSubcategory.thick_cl (I : Set C) : ThickSubcategory C where
  carrier := thick_cl' I
  zero_mem' := ⟨_, ⟨0, rfl⟩, smd.of_mem (addc.of_mem rfl)⟩
  shift_mem' {i a} := fun ⟨_, ⟨n, rfl⟩, ha⟩ => ⟨_, ⟨n, rfl⟩, le_shift (⟪I⟫' n) _ _ ha⟩
  iso_mem' {a b} := fun ⟨_, ⟨n, rfl⟩, ha⟩ ⟨φ⟩ => ⟨_, ⟨n, rfl⟩, of_iso (P := ⟪I⟫' n) φ ha⟩
  obj₃_mem' hT := fun ⟨_, ⟨n, rfl⟩, h₁⟩ ⟨_, ⟨m, rfl⟩, h₂⟩ => by
    refine ⟨_, ⟨m + n, rfl⟩, ?_⟩
    show _ ∈ ⟪I⟫' (m + n)
    rw [←level_dia_level]
    apply star_subset_dia
    rw [star_eq₃]
    exact ⟨_, h₁, _, h₂, _, _, _, hT⟩
  smd_mem' {a b} := fun ⟨_, ⟨n, rfl⟩, ha⟩ => ⟨_, ⟨n, rfl⟩, level_of_smd_left n ha⟩


end props

/- 3-19 TODO
  · G generator ↔ ∀ support datum supp G = supp T
  · Def of dimension
  · Dense Functors and dimension decreasing
-/
