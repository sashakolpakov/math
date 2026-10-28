import OAI.NumberTheory.PadicHodge.IntegralComparison.Geometric.AffineHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.FormalCoproductQuasiIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Total
import OAI.NumberTheory.PadicHodge.GeometricComparison.TotalFlip
import OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexMap

/-! # Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.QuasiIso

noncomputable section

/-! A quasi-isomorphism of quasicoherent sheaf complexes induces a
quasi-isomorphism of their native ordered affine Čech totals. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false

universe u

variable {X S : Scheme.{u}} (π : X ⟶ S)
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
  {K L : CochainComplex X.Modules ℕ} (f : K ⟶ L)

def bicomplexMap : Total.Comparison.bicomplex π U K ⟶
    Total.Comparison.bicomplex π U L :=
  ((AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor π U).mapHomologicalComplex (.up ℕ)).map f

def map : (Total.Comparison.bicomplex π U K).total (.up ℕ) ⟶
    (Total.Comparison.bicomplex π U L).total (.up ℕ) :=
  HomologicalComplex₂.total.map (bicomplexMap π U f) (.up ℕ)

theorem column_quasiIso (p : ℕ)
    (hf : ∀ i : AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι p,
      QuasiIso (((Geometric.AffineHomology.sections π
        (∏ᶜ fun k : Fin (p + 1) => U (i.val k))).mapHomologicalComplex (.up ℕ)).map f)) :
    QuasiIso ((GeometricComparison.TotalFlip.TotalFlipNaturality.flipped (bicomplexMap π U f)).f p) :=
  FormalCoproductQuasiIso.quasiIso Γ(S, ⊤) (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedCechFormalObject U p)
    (((AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheafFunctor π).mapHomologicalComplex (.up ℕ)).map f) hf

theorem quasiIso_of_sections
    (hf : ∀ (p : ℕ) (i : AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι p),
      QuasiIso (((Geometric.AffineHomology.sections π
        (∏ᶜ fun k : Fin (p + 1) => U (i.val k))).mapHomologicalComplex (.up ℕ)).map f)) :
    QuasiIso (OrderedCech.QuasiIso.map π U f) := by
  have : QuasiIso (HomologicalComplex₂.total.map
      (GeometricComparison.TotalFlip.TotalFlipNaturality.flipped (bicomplexMap π U f)) (.up ℕ)) :=
    AlgebraicTopology.DeRham.Comparison.DoubleComplexMap.DoubleComplex.total_map_quasiIso_of_columns _
      (fun p => column_quasiIso π U f p (hf p))
  constructor
  intro n
  exact (GeometricComparison.TotalFlip.TotalFlipNaturality.quasiIsoAt_iff (bicomplexMap π U f) n).mp inferInstance

theorem quasiIso [X.IsSeparated] (hU : ∀ i, IsAffineOpen (U i))
    [∀ n, (K.X n).IsQuasicoherent] [∀ n, (L.X n).IsQuasicoherent] [QuasiIso f] :
    QuasiIso (OrderedCech.QuasiIso.map π U f) :=
  quasiIso_of_sections π U f (fun p i =>
    Geometric.AffineHomology.quasiIso π _
      (AlgebraicGeometry.SheafCohomology.Cech.Cochains.IsAffineOpen.cechIntersection U hU p i.val) f)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.QuasiIso
