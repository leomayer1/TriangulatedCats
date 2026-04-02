import TriangulatedCats.Generator
import Mathlib.CategoryTheory.ComposableArrows.Basic
import Mathlib.CategoryTheory.Functor.OfSequence

open CategoryTheory
open Limits Category Preadditive Pretriangulated ZeroObject ObjectProperty

variable {C : Type*} [Category C] [Preadditive C]
variable {I J K : Set C}
variable {a b c : C} (G : C) {f : a ⟶ b} {g : b ⟶ c}

def isGhost (I : Set C) (f : a ⟶ b) := ∀ d ∈ I, ∀ h : d ⟶ a, h ≫ f = 0

structure Ghost (I : Set C) (a : C) where
b : C
f : a ⟶ b
isGhost : isGhost I f

structure PseudoAdjoint (I : Set C) (a : C) where
  x : C
  hx : x ∈ I
  f : x ⟶ a
  prop : ∀ d ∈ I, ∀ h : d ⟶ a, ∃ g : d ⟶ x, h = g ≫ f

/-
  Given objects G, a, and a natural n, this is a sequence
  a_0 → a_1 → … → a_n of G-ghost maps
-/
def ghostSeqObj (I : Set C) (a : C) (A : (x : C) → (Ghost I x)) : (n : ℕ) → C
| 0 => a
| n + 1 => (A (ghostSeqObj I a A n)).b

def ghostSeqHom (I : Set C) (a : C) (A : (x : C) → (Ghost I x)) (n : ℕ) :
    (ghostSeqObj I a A n) ⟶ (ghostSeqObj I a A (n + 1)) := (A (ghostSeqObj I a A n)).f

def ghostSeq (I : Set C) (a : C) (A : (x : C) → (Ghost I x)) : ℕ ⥤ C :=
    Functor.ofSequence (ghostSeqHom I a A)

@[simp]
theorem ghostSeqHom_eq {A : (x : C) → (Ghost I x)} {n : ℕ} {φ : n ⟶ n + 1} : (ghostSeq I a A).map φ =
    (A (ghostSeqObj I a A n)).f := Functor.ofSequence_map_homOfLE_succ (ghostSeqHom I a A) n

variable [HasZeroObject C]

theorem isGhost_isZero : isGhost IsZero f := fun _ hd _ =>
  zero_of_source_iso_zero _ (IsZero.isoZero hd)

variable [HasShift C ℤ] [∀ n : ℤ, Functor.Additive (shiftFunctor C n)]
variable [Pretriangulated C]

theorem isGhost_star (hf : isGhost I f) (hg : isGhost J g) : isGhost (I ⋆ J) (f ≫ g) := by
  rintro c ⟨_, ha, _, hb, j, _, _, H⟩ α
  obtain ⟨β, hβ⟩ := Triangle.yoneda_exact₂ _ H (α ≫ f) (by rw [←assoc]; exact hf _ ha _)
  rw [←assoc, hβ, assoc, hg _ hb _, comp_zero]

theorem isGhost_addc [IsStableUnderShift I ℤ] (hf : isGhost I f) : isGhost (addc I) f := by
  open IsStableUnderShift in
  suffices H : ∀ d ∈ (addc I), ∀ (i : ℤ),  ∀ h : d⟦i⟧ ⟶ a, h ≫ f = 0 from fun d hd h => by
    rw [←IsIso.comp_left_eq_zero ((shiftFunctorZero C ℤ).hom.app d), ←assoc, H d hd]
  intro d hd i h
  induction hd generalizing i with
  | zero => exact zero_of_source_iso_zero _ (IsZero.isoZero (Functor.map_isZero _ (isZero_zero _)))
  | of_mem' d hd => exact hf _ (le_shift (P := I) _ d hd) h
  | of_shift' j d hd ih =>
    rw [←IsIso.comp_left_eq_zero ((shiftFunctorAdd C j i).hom.app d), ←assoc, ih]
  | of_iso' _ _ _ φ ih => rw [←IsIso.comp_left_eq_zero ((φ.hom)⟦i⟧') (h ≫ f), ←assoc, ih]
  | biprod' d d' _ _ ihd ihd' =>
    have := preservesBinaryBiproducts_of_preservesBinaryProducts (shiftFunctor C i)
    rw [←IsIso.comp_left_eq_zero (Functor.mapBiprod (shiftFunctor C i) d d').inv]
    have h₁ : biprod.inl ≫ ((shiftFunctor C i).mapBiprod d d').inv ≫ h ≫ f = 0 := by
      rw [←assoc, ←assoc, ihd]
    have h₂ : biprod.inr ≫ ((shiftFunctor C i).mapBiprod d d').inv ≫ h ≫ f = 0 := by
      rw [←assoc, ←assoc, ihd']
    cat_disch

theorem isGhost_smd (hf : isGhost I f) : isGhost (smd I) f := by
  intro d hd h
  induction hd with
  | of_mem' _ ha => exact hf _ ha h
  | of_smd_left' d d' _ ih =>
    rw [←id_comp h, ←biprod.inl_fst (Y := d'), assoc _ _ h, assoc, ih (biprod.fst ≫ h), comp_zero]
  | of_smd_right' d d' _ ih =>
    rw [←id_comp h, ←biprod.inr_snd (X := d), assoc _ _ h, assoc, ih (biprod.snd ≫ h), comp_zero]

theorem isGhost_dia [IsStableUnderShift I ℤ] [IsStableUnderShift J ℤ]
    (hf : isGhost I f) (hg : isGhost J g) : isGhost (I ⋄ J) (f ≫ g) := by
  apply isGhost_smd (isGhost_star (isGhost_addc hf) (isGhost_addc hg))

theorem isGhost_level [IsStableUnderShift I ℤ] (hf : isGhost I f) : isGhost (⟪I⟫' 1) f := by
  rw [level_one]
  exact isGhost_smd (isGhost_addc hf)


noncomputable
def PA_Triangle (A : PseudoAdjoint I a) : Triangle C :=
  Triangle.mk A.f (Exists.choose (Exists.choose_spec (distinguished_cocone_triangle A.f)))
    (Exists.choose (Exists.choose_spec (Exists.choose_spec (distinguished_cocone_triangle A.f))))

theorem dist_PA_Triangle (A : PseudoAdjoint I a) : PA_Triangle A ∈ distTriang C :=
  Exists.choose_spec (Exists.choose_spec (Exists.choose_spec (distinguished_cocone_triangle A.f)))

@[simp]
theorem dist_PA_Triangle_obj₁ (A : PseudoAdjoint I a) : (PA_Triangle A).obj₁ = A.x := rfl

@[simp]
theorem dist_PA_Triangle_obj₂ (A : PseudoAdjoint I a) : (PA_Triangle A).obj₂ = a := rfl

@[simp]
theorem dist_PA_Triangle_mor₁ (A : PseudoAdjoint I a) : (PA_Triangle A).mor₁ = A.f := rfl

@[simps]
noncomputable
def GH_of_PA (A : PseudoAdjoint I a) : Ghost I a where
b := (PA_Triangle A).obj₃
f := (PA_Triangle A).mor₂
isGhost d hd α := by
  obtain ⟨β, hβ⟩ := A.prop d hd α
  have hfg : A.f ≫ _ = 0 := comp_distTriang_mor_zero₁₂ _ (dist_PA_Triangle A)
  rw [hβ, assoc, hfg, comp_zero]


omit [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive]
    [Pretriangulated C] [HasZeroObject C] in
theorem ghostSeqHomGhost {A : (x:  C) → (Ghost I x)} {n : ℕ} {φ : n ⟶ n + 1} :
    isGhost I ((ghostSeq I a A).map φ) := by
  convert (A (ghostSeqObj I a A n)).isGhost
  convert Functor.ofSequence_map_homOfLE_succ (ghostSeqHom I a A) n

theorem ghostSeqGhostLevel [IsStableUnderShift I ℤ] {a : C} {A : (x : C) → (Ghost I x)}
    {n : ℕ} {N : 0 ⟶ n}: isGhost (⟪I⟫' n) ((ghostSeq I a A).map N) := by
  induction n with
  | zero =>
    rw [level_zero]
    exact isGhost_isZero
  | succ n ih =>
    have H : N = (⟨⟨Nat.zero_le n⟩⟩ : 0 ⟶ n) ≫ (⟨⟨Nat.le_succ n⟩⟩ : n ⟶ n + 1) := rfl
    rw [H, level, Functor.map_comp]
    apply isGhost_dia ih
    apply ghostSeqHomGhost

variable [IsTriangulated C]

theorem ghostSeqConeLevel {a : C} {A : (x : C) → PseudoAdjoint I x} {n : ℕ} {φ : 0 ⟶ n} :
    ∀ c : C, ∀ (f : _ ⟶ c) g, Triangle.mk
    ((ghostSeq I a (fun x => GH_of_PA (A x))).map φ) f g ∈ distTriang C → c ∈ ⟪I⟫' n := by
  induction n with
  | zero =>
    have hφ : φ = 𝟙 _ := rfl
    intro c f g H
    rw [hφ, CategoryTheory.Functor.map_id] at H
    rw [level_zero]
    exact (Triangle.isZero₃_iff_isIso₁ _ H).mpr (IsIso.id _)
  | succ n ih =>
    let φ₁ : 0 ⟶ n := ⟨⟨by lia⟩⟩
    let φ₂ : n ⟶ (n + 1) := ⟨⟨by lia⟩⟩
    have hφ : φ = φ₁ ≫ φ₂ := rfl
    let F := (ghostSeq I a (fun x => GH_of_PA (A x)))
    intro c g h H
    obtain ⟨c₁, g₁, h₁, H₁⟩ := distinguished_cocone_triangle (F.map φ₁)
    obtain ⟨c₂, g₂, h₂, H₂⟩ := distinguished_cocone_triangle (F.map φ₂)
    obtain ⟨O⟩  := IsTriangulated.octahedron_axiom (Functor.map_comp _ _ _).symm H₁ H₂ H
    have hc₁ : c₁ ∈ ⟪I⟫' n := ih _ _ _ H₁
    have hc₂ : c₂ ∈ ⟪I⟫' 1 := by
      let ψ : (A (F.obj n)).x⟦(1 : ℤ)⟧ ≅ c₂ := by
        let hT := dist_PA_Triangle (A (F.obj n))
        let Φ := isoTriangleOfIso₁₂ _ _ (rot_of_distTriang _ hT) H₂ (Iso.refl _) (Iso.refl _) (by aesop)
        exact Triangle.π₃.mapIso Φ
      apply IsClosedUnderIsomorphisms.of_iso (P := ⟪I⟫' 1) ψ
      apply le_shift (P := ⟪I⟫' 1) (1 : ℤ)
      rw [level_one]
      apply smd.of_mem (addc.of_mem (A (F.obj n)).hx)
    rw [level, dia, ←smd_star_smd, ←level_one, addc_eq_self]
    apply smd.of_mem
    exact ⟨_,hc₁,_,hc₂,_,_, _, O.mem⟩

variable [IsStableUnderShift I ℤ]

theorem mem_level_iff_ghostSeq (A : (x : C) → PseudoAdjoint I x) {n : ℕ} {φ : 0 ⟶ n} :
    a ∈ (⟪I⟫' n) ↔ ((ghostSeq I a (fun x => GH_of_PA (A x))).map ⟨⟨Nat.zero_le n⟩⟩) = 0 := by
  constructor
  . intro ha
    rw [←id_comp ((ghostSeq I a fun x ↦ GH_of_PA (A x)).map _)]
    exact ghostSeqGhostLevel a ha (𝟙 a)
  . open IsClosedUnderSmd IsClosedUnderIsomorphisms IsStableUnderShift in
    intro ha
    suffices h : a⟦(1 : ℤ)⟧ ∈ ⟪I⟫' n from
      of_iso (P := ⟪I⟫' n) (shiftShiftNeg a (1 : ℤ)) (le_shift (P := ⟪I⟫' n) (-1) _ h)
    apply of_smd_right (P := ⟪I⟫' n)
    obtain ⟨Z, g, h, H⟩ := distinguished_cocone_triangle ((ghostSeq I a (fun x => GH_of_PA (A x))).map φ)
    obtain ⟨e : Z ≅ _ ⊞ _, _⟩ := exists_iso_binaryBiproduct_of_distTriang _ (rot_of_distTriang _ H)
      (neg_eq_zero.mpr (by
      have H : (Triangle.mk ((ghostSeq I a fun x ↦ GH_of_PA (A x)).map φ) g h).mor₁ = 0 := ha
      rw [H]
      exact Functor.map_zero (shiftFunctor C (1 : ℤ)) _ _
      ))
    apply of_iso (P := ⟪I⟫' n) e (ghostSeqConeLevel (φ := φ) Z g h H)
