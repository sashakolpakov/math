import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.FrobeniusCharts
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.ModuleGenerators
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.CoherentFiniteness

/-! # Frobenius Coherence -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.FrobeniusCoherence

noncomputable section

/-!
# IntegralComparison: coherence of the original global Frobenius de Rham terms and projective cohomology finiteness
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (k : Type u) [Field k] [Fintype k] (X : Over (Spec (CommRingCat.of k)))
  [IsProper X.hom] [Smooth X.hom]

abbrev term (n : ℕ) : X.left.Modules := (Frobenius.DeRhamGlobal.complex k X).X n

omit [Fintype k] in
theorem cover : (Opens.grothendieckTopology X.left).CoversTop (FrobeniusCharts.opens k X) := by
  rw [Opens.coversTop_iff]
  exact FrobeniusCharts.cover k X

theorem open_quasicoherent (i : EtaleCover.Index k X) (n : ℕ) :
    ((term k X n).over (FrobeniusCharts.opens k X i)).IsQuasicoherent := by
  let U := FrobeniusCharts.opens k X i
  let hU : IsAffineOpen U := FrobeniusCharts.affine k X i
  let : IsAffine U.toScheme := hU
  let : ((term k X n).restrict hU.fromSpec).IsQuasicoherent := FrobeniusCharts.quasicoherent k X i n
  let : ((term k X n).restrict U.ι).IsQuasicoherent := AffineOpen.ModuleGenerators.quasicoherent (term k X n) U hU
  exact AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_over_of_restrict_of_isAffineOpen (term k X n) U

theorem quasicoherent (n : ℕ) : (term k X n).IsQuasicoherent :=
  @SheafOfModules.IsQuasicoherent.of_coversTop _ _ _ _ _ _ _ _ (term k X n) _
    (FrobeniusCharts.opens k X) (cover k X) (fun i => open_quasicoherent k X i n)

theorem chart_generators (i : EtaleCover.Index k X) (n : ℕ) :
    ∃ G : ((term k X n).restrict (FrobeniusCharts.affine k X i).fromSpec).GeneratingSections,
      G.IsFiniteType := by
  let : (FrobeniusCharts.restricted k X i n).IsQuasicoherent :=
    FrobeniusCharts.quasicoherent k X i n
  let : (FrobeniusCharts.restricted k X i n).IsFiniteType :=
    FrobeniusCharts.finiteType k X i n
  exact AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.exists_generatingSections_of_isFiniteType_of_isAffine
    (FrobeniusCharts.restricted k X i n)

theorem open_generators (i : EtaleCover.Index k X) (n : ℕ) :
    ∃ G : ((term k X n).restrict (FrobeniusCharts.opens k X i).ι).GeneratingSections,
      G.IsFiniteType := by
  obtain ⟨G, hG⟩ := chart_generators k X i n
  let : G.IsFiniteType := hG
  exact ⟨AffineOpen.ModuleGenerators.generatingSections (term k X n)
    (FrobeniusCharts.opens k X i) (FrobeniusCharts.affine k X i) G,
    AffineOpen.ModuleGenerators.generatingSections_finite (term k X n)
      (FrobeniusCharts.opens k X i) (FrobeniusCharts.affine k X i) G⟩

theorem finiteType (n : ℕ) : (term k X n).IsFiniteType := by
  choose G hG using fun i => open_generators k X i n
  let q : (term k X n).LocalGeneratorsData :=
    { I := EtaleCover.Index k X
      X := FrobeniusCharts.opens k X
      coversTop := cover k X
      generators := fun i => AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.generatingSectionsOverOfRestrict (term k X n)
        (FrobeniusCharts.opens k X i) (G i) }
  have hq : q.IsFiniteType := by
    constructor
    intro i
    let : (G i).IsFiniteType := hG i
    exact AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.generatingSectionsOverOfRestrict_isFiniteType (term k X n)
      (FrobeniusCharts.opens k X i) (G i)
  refine { exists_localGeneratorsData := ?_ }
  exact ⟨q, hq⟩

theorem cohomology_finite (hprojective : Projectivity.Construction.ProjectiveOver k X.hom) (n q : ℕ) :
    letI := Projective.CoherentFiniteness.coefficientModule k X.hom (term k X n) q
    Module.Finite k (AlgebraicGeometry.SheafCohomology.AffineH.Projective.H (term k X n) q) := by
  let : (term k X n).IsQuasicoherent := quasicoherent k X n
  let : (term k X n).IsFiniteType := finiteType k X n
  exact Projective.CoherentFiniteness.cohomology_finite k X.hom hprojective (term k X n) q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.FrobeniusCoherence
