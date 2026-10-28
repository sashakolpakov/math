import OAI.AlgebraicGeometry.Crystalline.Cohomology.ProperOrdinaryFormCharts
import OAI.AlgebraicGeometry.Crystalline.Cohomology.OrdinaryFormSheaf
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ProperCoherentCoefficient
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.ModuleGenerators

/-! # Proper Ordinary Form Finiteness -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.ProperOrdinaryFormFiniteness.SmoothProperOrdinaryFormFiniteness

noncomputable section

/-! # Proper coherent cohomology of the original ordinary differential-form modules -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (k : Type u) [Field k] (X : Over (Spec (CommRingCat.of k)))
  [IsProper X.hom] [Smooth X.hom]

abbrev term (n : ℕ) : X.left.Modules := OrdinaryFormBase.OrdinaryFormModulePresheaf.sheaf k X n

theorem cover : (Opens.grothendieckTopology X.left).CoversTop (ProperOrdinaryFormCharts.SmoothProperOrdinaryFormCharts.opens k X) := by
  rw [Opens.coversTop_iff]
  exact ProperOrdinaryFormCharts.SmoothProperOrdinaryFormCharts.cover k X

theorem open_quasicoherent (i : NumberTheory.PadicHodge.IntegralComparison.SmoothProper.EtaleCover.Index k X) (n : ℕ) :
    ((term k X n).over (ProperOrdinaryFormCharts.SmoothProperOrdinaryFormCharts.opens k X i)).IsQuasicoherent := by
  let U := ProperOrdinaryFormCharts.SmoothProperOrdinaryFormCharts.opens k X i
  let hU : IsAffineOpen U := ProperOrdinaryFormCharts.SmoothProperOrdinaryFormCharts.affine k X i
  let : IsAffine U.toScheme := hU
  let : ((term k X n).restrict hU.fromSpec).IsQuasicoherent :=
    ProperOrdinaryFormCharts.SmoothProperOrdinaryFormCharts.quasicoherent k X i n
  let : ((term k X n).restrict U.ι).IsQuasicoherent := NumberTheory.PadicHodge.IntegralComparison.AffineOpen.ModuleGenerators.quasicoherent (term k X n) U hU
  exact SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_over_of_restrict_of_isAffineOpen (term k X n) U

theorem quasicoherent (n : ℕ) : (term k X n).IsQuasicoherent :=
  @SheafOfModules.IsQuasicoherent.of_coversTop _ _ _ _ _ _ _ _ (term k X n) _
    (ProperOrdinaryFormCharts.SmoothProperOrdinaryFormCharts.opens k X) (cover k X) (fun i => open_quasicoherent k X i n)

theorem chart_generators (i : NumberTheory.PadicHodge.IntegralComparison.SmoothProper.EtaleCover.Index k X) (n : ℕ) :
    ∃ G : ((term k X n).restrict (ProperOrdinaryFormCharts.SmoothProperOrdinaryFormCharts.affine k X i).fromSpec).GeneratingSections,
      G.IsFiniteType := by
  let : (ProperOrdinaryFormCharts.SmoothProperOrdinaryFormCharts.restricted k X i n).IsQuasicoherent :=
    ProperOrdinaryFormCharts.SmoothProperOrdinaryFormCharts.quasicoherent k X i n
  let : (ProperOrdinaryFormCharts.SmoothProperOrdinaryFormCharts.restricted k X i n).IsFiniteType :=
    ProperOrdinaryFormCharts.SmoothProperOrdinaryFormCharts.finiteType k X i n
  exact SheafCohomology.Projective.Quasicoherent.Scheme.Modules.exists_generatingSections_of_isFiniteType_of_isAffine
    (ProperOrdinaryFormCharts.SmoothProperOrdinaryFormCharts.restricted k X i n)

theorem open_generators (i : NumberTheory.PadicHodge.IntegralComparison.SmoothProper.EtaleCover.Index k X) (n : ℕ) :
    ∃ G : ((term k X n).restrict (ProperOrdinaryFormCharts.SmoothProperOrdinaryFormCharts.opens k X i).ι).GeneratingSections,
      G.IsFiniteType := by
  obtain ⟨G, hG⟩ := chart_generators k X i n
  let : G.IsFiniteType := hG
  exact ⟨NumberTheory.PadicHodge.IntegralComparison.AffineOpen.ModuleGenerators.generatingSections (term k X n)
    (ProperOrdinaryFormCharts.SmoothProperOrdinaryFormCharts.opens k X i) (ProperOrdinaryFormCharts.SmoothProperOrdinaryFormCharts.affine k X i) G,
    NumberTheory.PadicHodge.IntegralComparison.AffineOpen.ModuleGenerators.generatingSections_finite (term k X n)
      (ProperOrdinaryFormCharts.SmoothProperOrdinaryFormCharts.opens k X i) (ProperOrdinaryFormCharts.SmoothProperOrdinaryFormCharts.affine k X i) G⟩

theorem finiteType (n : ℕ) : (term k X n).IsFiniteType := by
  choose G hG using fun i => open_generators k X i n
  let q : (term k X n).LocalGeneratorsData := {
    I := NumberTheory.PadicHodge.IntegralComparison.SmoothProper.EtaleCover.Index k X
    X := ProperOrdinaryFormCharts.SmoothProperOrdinaryFormCharts.opens k X
    coversTop := cover k X
    generators := fun i => SheafCohomology.Projective.Quasicoherent.Scheme.Modules.generatingSectionsOverOfRestrict (term k X n)
      (ProperOrdinaryFormCharts.SmoothProperOrdinaryFormCharts.opens k X i) (G i) }
  have hq : q.IsFiniteType := by
    constructor
    intro i
    let : (G i).IsFiniteType := hG i
    exact SheafCohomology.Projective.Quasicoherent.Scheme.Modules.generatingSectionsOverOfRestrict_isFiniteType (term k X n)
      (ProperOrdinaryFormCharts.SmoothProperOrdinaryFormCharts.opens k X i) (G i)
  refine { exists_localGeneratorsData := ?_ }
  exact ⟨q, hq⟩

theorem cohomology_finite (n q : ℕ) :
    letI := NumberTheory.PadicHodge.IntegralComparison.Projective.CoherentFiniteness.coefficientModule k X.hom (term k X n) q
    Module.Finite k (SheafCohomology.AffineH.Projective.H (term k X n) q) := by
  let : (term k X n).IsQuasicoherent := quasicoherent k X n
  let : (term k X n).IsFiniteType := finiteType k X n
  exact ProperCoherentCoefficient.ProperCoherentFiniteness.coefficient k X.hom (term k X n) q

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.ProperOrdinaryFormFiniteness.SmoothProperOrdinaryFormFiniteness
