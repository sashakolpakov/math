import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechCoverHomology

/-! # Affine Cover Model -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineCoverModel.Construction.AffineCoverPerfectModel

noncomputable section

/-! A finite projective model for any finite affine cover of a flat
projective family over a Noetherian affine base. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

variable {X S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)] [X.IsSeparated]
variable (π : X ⟶ S) [Flat π] (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation (Over.mk π))
variable {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
variable (hU : iSup U = ⊤) (ha : ∀ i, IsAffineOpen (U i))

include P hU ha

theorem exists_model (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) :
    ∃ (D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ)
      (φ : D ⟶ SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π L.sheaf U),
      QuasiIso φ ∧
      (∃ N, ∀ q, N ≤ q → IsZero (D.X q)) ∧
      (∀ q, Module.Finite Γ(S, ⊤) (D.X q)) ∧
      (∀ q, Module.Projective Γ(S, ⊤) (D.X q)) ∧
      (∀ (A : Type u) [AddCommGroup A] [Module Γ(S, ⊤) A],
        QuasiIso (ModuleTensor.Construction.ModuleTensorFunctor.map A φ)) := by
  let : Fintype ι := Fintype.ofFinite ι
  apply BoundedProjectiveComplex.Construction.CochainFiniteModel.exists_finite_projective_complex (SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π L.sheaf U)
  · exact ⟨Fintype.card ι, SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechObject_isZero_of_card_le π L.sheaf U⟩
  · exact fun q => OrderedCechObject.Construction.OrderedCechFlat.complex π L.sheaf (LineBundleFree.Construction.LineBundleCoherence.invertible L)
      U (fun q i => SheafCohomology.Cech.Cochains.IsAffineOpen.cechIntersection U ha q i) q
  · exact fun q => CechCoverHomology.Construction.CechCoverFiniteness.projective π U hU ha P L q

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineCoverModel.Construction.AffineCoverPerfectModel
