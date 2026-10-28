import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Augmentation
import OAI.NumberTheory.PadicHodge.PeriodInvariants.TotalEdgeZeroComparison

/-! # Total -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Total.Comparison

noncomputable section

/-! A complex whose terms have no higher ordered Čech cohomology is
computed by its native Čech total complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

universe u

variable {X S : Scheme.{u}} (π : X ⟶ S)
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

def bicomplex (K : CochainComplex X.Modules ℕ) :
    HomologicalComplex₂ (ModuleCat.{u} Γ(S, ⊤)) (.up ℕ) (.up ℕ) :=
  ((AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor π U).mapHomologicalComplex (.up ℕ)).obj K

def sectionComplex (K : CochainComplex X.Modules ℕ) : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ :=
  ((Augmentation.sections π).mapHomologicalComplex (.up ℕ)).obj K

def edge (K : CochainComplex X.Modules ℕ) (hU : iSup U = ⊤) :
    sectionComplex π K ⟶ (Comparison.bicomplex π U K).total (.up ℕ) :=
  (AlgebraicGeometry.SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge (bicomplex π U K)) (sectionComplex π K)
    (fun q => Augmentation.map π U (K.X q))
    (fun q q' _ => (Augmentation.naturality π U (K.d q q')).symm)
    (fun q => Augmentation.map_d π U (K.X q) hU)

theorem quasiIso (K : CochainComplex X.Modules ℕ) (hU : iSup U = ⊤)
    (hK : ∀ q p, IsZero ((AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π (K.X q) U).homology (p + 1))) :
    QuasiIso (edge π U K hU) := by
  let B := Comparison.bicomplex π U K
  let A := sectionComplex π K
  let e := fun q => Augmentation.map π U (K.X q)
  have he : ∀ q q', (ComplexShape.up ℕ).Rel q q' →
      e q ≫ (B.d q q').f 0 = A.d q q' ≫ e q' :=
    fun q q' _ => (Augmentation.naturality π U (K.d q q')).symm
  have w : ∀ q, e q ≫ (B.X q).d 0 1 = 0 :=
    fun q => Augmentation.map_d π U (K.X q) hU
  have haug : ∀ q, (ShortComplex.mk (e q) ((B.X q).d 0 1) (w q)).Exact :=
    fun q => Augmentation.exact π U (K.X q) hU
  have hmono : ∀ q, Mono (e q) := fun q => Augmentation.map_mono π U (K.X q) hU
  have hrows : PeriodInvariants.ModuleTotalEdgeComparison.RowsExact B := by
    intro q p
    exact ((B.X q).exactAt_iff' p (p + 1) (p + 2) (by simp) (by simp)).mp
      ((HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr (hK q p))
  rw [_root_.quasiIso_iff]
  intro n
  cases n with
  | zero =>
    let : Mono (e 0) := hmono 0
    let : Mono (e 1) := hmono 1
    exact PeriodInvariants.TotalEdgeZeroComparison.horizontal B A e he w (haug 0)
  | succ n => exact PeriodInvariants.ModuleTotalEdgeComparison.horizontal B A e he w haug hmono hrows n

def homologyIso (K : CochainComplex X.Modules ℕ) (hU : iSup U = ⊤)
    (hK : ∀ q p, IsZero ((AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π (K.X q) U).homology (p + 1)))
    (n : ℕ) :
    (sectionComplex π K).homology n ≅ ((Comparison.bicomplex π U K).total (.up ℕ)).homology n := by
  letI := quasiIso π U K hU hK
  exact isoOfQuasiIsoAt (edge π U K hU) n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Total.Comparison
