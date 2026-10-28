import OAI.NumberTheory.PadicHodge.IntegralComparison.Coherent.CoherentPullback
import OAI.NumberTheory.PadicHodge.IntegralComparison.KernelTowerMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.NegativeResolution

/-! # Negative Common Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeCommonRefinement

noncomputable section

/-! Two coherent kernel resolutions admit a common negative-twist
refinement over any specified pair of maps from the initial sheaf.
The construction uses coherent pullbacks, so it does not require the
negative twists to be projective objects of the sheaf category. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial

set_option backward.isDefEq.respectTransparency false

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {σ : Type} [Fintype σ]

attribute [local instance] MvPolynomial.gradedAlgebra

local instance : LocallyOfFiniteType (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) :=
  AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ_locallyOfFiniteType

local instance : IsLocallyNoetherian (Proj (homogeneousSubmodule σ R)) :=
  LocallyOfFiniteType.isLocallyNoetherian (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))

abbrev Tower := KernelTowerResolution.Tower (C := (Proj (homogeneousSubmodule σ R)).Modules)

structure State (T U : Tower (R := R) (σ := σ)) (n : ℕ) where
  module : (Proj (homogeneousSubmodule σ R)).Modules
  quasicoherent : module.IsQuasicoherent
  finiteType : module.IsFiniteType
  left : module ⟶ T.object n
  right : module ⟶ U.object n

attribute [instance] State.quasicoherent State.finiteType

namespace State

variable {T U : Tower (R := R) (σ := σ)}
  [∀ n, (T.object n).IsQuasicoherent] [∀ n, (U.object n).IsQuasicoherent]
  [∀ n, (T.term n).IsQuasicoherent] [∀ n, (U.term n).IsQuasicoherent]
  [∀ n, (T.term n).IsFiniteType] [∀ n, (U.term n).IsFiniteType]
  {n : ℕ} (s : State T U n)

abbrev leftPullback := pullback s.left (T.projection n)

instance leftPullback_quasicoherent : s.leftPullback.IsQuasicoherent :=
  Coherent.CoherentPullback.quasicoherent s.left (T.projection n)

instance leftPullback_finiteType : s.leftPullback.IsFiniteType :=
  Coherent.CoherentPullback.finiteType s.left (T.projection n)

abbrev rightPullback := pullback (pullback.fst s.left (T.projection n) ≫ s.right) (U.projection n)

instance rightPullback_quasicoherent : s.rightPullback.IsQuasicoherent :=
  Coherent.CoherentPullback.quasicoherent _ (U.projection n)

instance rightPullback_finiteType : s.rightPullback.IsFiniteType :=
  Coherent.CoherentPullback.finiteType _ (U.projection n)

variable (j : σ) (B : ℕ)

def cover := Projective.NegativeResolution.presentation s.rightPullback j B

def projection : (s.cover j B).source ⟶ s.module :=
  (s.cover j B).projection ≫ pullback.fst _ _ ≫ pullback.fst _ _

instance projection_epi : Epi (s.projection j B) := by
  dsimp only [State.projection]
  infer_instance

def leftMap : (s.cover j B).source ⟶ T.term n :=
  (s.cover j B).projection ≫ pullback.fst _ _ ≫ pullback.snd _ _

def rightMap : (s.cover j B).source ⟶ U.term n :=
  (s.cover j B).projection ≫ pullback.snd _ _

theorem left_projection : s.leftMap j B ≫ T.projection n = s.projection j B ≫ s.left := by
  simp only [State.leftMap, State.projection, Category.assoc, pullback.condition]

theorem right_projection : s.rightMap j B ≫ U.projection n = s.projection j B ≫ s.right := by
  simp only [State.rightMap, State.projection, Category.assoc, pullback.condition]

def next : State T U (n + 1) where
  module := kernel (s.projection j B)
  quasicoherent := AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_kernel (s.projection j B)
  finiteType := AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isFiniteType_kernel (s.projection j B)
  left := kernel.lift (T.projection n) (kernel.ι (s.projection j B) ≫ s.leftMap j B) (by
    rw [Category.assoc, s.left_projection, ← Category.assoc, kernel.condition, zero_comp]) ≫
      (T.kernelIso n).inv
  right := kernel.lift (U.projection n) (kernel.ι (s.projection j B) ≫ s.rightMap j B) (by
    rw [Category.assoc, s.right_projection, ← Category.assoc, kernel.condition, zero_comp]) ≫
      (U.kernelIso n).inv

theorem next_left : (s.next j B).left ≫ T.inclusion n =
    kernel.ι (s.projection j B) ≫ s.leftMap j B := by
  simp only [State.next, KernelTowerResolution.Tower.inclusion, Category.assoc,
    Iso.inv_hom_id_assoc, kernel.lift_ι]

theorem next_right : (s.next j B).right ≫ U.inclusion n =
    kernel.ι (s.projection j B) ≫ s.rightMap j B := by
  simp only [State.next, KernelTowerResolution.Tower.inclusion, Category.assoc,
    Iso.inv_hom_id_assoc, kernel.lift_ι]

end State

variable (T U : Tower (R := R) (σ := σ))
  [∀ n, (T.object n).IsQuasicoherent] [∀ n, (U.object n).IsQuasicoherent]
  [∀ n, (T.term n).IsQuasicoherent] [∀ n, (U.term n).IsQuasicoherent]
  [∀ n, (T.term n).IsFiniteType] [∀ n, (U.term n).IsFiniteType]
  (j : σ) (B : ℕ)
  (M : (Proj (homogeneousSubmodule σ R)).Modules) [M.IsQuasicoherent] [M.IsFiniteType]
  (a : M ⟶ T.object 0) (b : M ⟶ U.object 0)

def state : (n : ℕ) → State T U n
  | 0 => ⟨M, inferInstance, inferInstance, a, b⟩
  | n + 1 => (state n).next j B

def tower : Tower (R := R) (σ := σ) where
  object n := (NegativeCommonRefinement.state T U j B M a b n).module
  term n := ((NegativeCommonRefinement.state T U j B M a b n).cover j B).source
  projection n := (NegativeCommonRefinement.state T U j B M a b n).projection j B
  epi _n := inferInstance
  kernelIso _n := Iso.refl _

def leftHom : KernelTowerMap.Hom (tower T U j B M a b) T where
  object n := (NegativeCommonRefinement.state T U j B M a b n).left
  term n := (NegativeCommonRefinement.state T U j B M a b n).leftMap j B
  projection n := (NegativeCommonRefinement.state T U j B M a b n).left_projection j B
  inclusion n := by
    simpa only [tower, KernelTowerResolution.Tower.inclusion, NegativeCommonRefinement.state,
      Iso.refl_hom, Category.id_comp] using (NegativeCommonRefinement.state T U j B M a b n).next_left j B

def rightHom : KernelTowerMap.Hom (tower T U j B M a b) U where
  object n := (NegativeCommonRefinement.state T U j B M a b n).right
  term n := (NegativeCommonRefinement.state T U j B M a b n).rightMap j B
  projection n := (NegativeCommonRefinement.state T U j B M a b n).right_projection j B
  inclusion n := by
    simpa only [tower, KernelTowerResolution.Tower.inclusion, NegativeCommonRefinement.state,
      Iso.refl_hom, Category.id_comp] using (NegativeCommonRefinement.state T U j B M a b n).next_right j B

instance left_quasiIso [IsIso a] : QuasiIso (leftHom T U j B M a b).chainMap := by
  let : IsIso ((leftHom T U j B M a b).object 0) := inferInstanceAs (IsIso a)
  infer_instance

instance right_quasiIso [IsIso b] : QuasiIso (rightHom T U j B M a b).chainMap := by
  let : IsIso ((rightHom T U j B M a b).object 0) := inferInstanceAs (IsIso b)
  infer_instance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeCommonRefinement
