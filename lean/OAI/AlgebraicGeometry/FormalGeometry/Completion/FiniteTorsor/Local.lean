import OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.ConstantScheme
import OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.Trivialization

/-! # Local -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor

noncomputable section

/-!
# Completion: finite-coefficient torsors are locally finite étale

The local trivializations are represented by actual finite disjoint unions
over the covering object. This proves local representability on a covering
sieve without assuming a global scheme representative.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (ℓ n : ℕ) {X : Scheme.{u}} (U : X.ProEt)

/-- The finite constant scheme over a site object, viewed in the slice of the site. -/
def Local.Construction.finiteCoefficientSlice : Over U := by
  let S := AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme U.left (ULift.{u} (ZMod (ℓ ^ n)))
  have : Etale S.hom := Finite.ConstantScheme.Construction.finiteConstantScheme_etale _ _
  let V : X.ProEt := Scheme.ProEt.mk (S.hom ≫ U.hom)
  exact Over.mk (MorphismProperty.Over.homMk (A := V) (B := U) S.hom rfl)

theorem Local.Construction.finiteCoefficientSlice_etale : Etale (Local.Construction.finiteCoefficientSlice ℓ n U).hom.left :=
  Finite.ConstantScheme.Construction.finiteConstantScheme_etale _ _

theorem Local.Construction.finiteCoefficientSlice_finite [NeZero (ℓ ^ n)] :
    IsFinite (Local.Construction.finiteCoefficientSlice ℓ n U).hom.left :=
  Finite.ConstantScheme.Construction.finiteConstantScheme_finite _ _

/-- A slice map to the coefficient object is a map of schemes over the covering object. -/
def Local.Construction.finiteCoefficientSliceHomEquiv (V : Over U) :
    (V ⟶ Local.Construction.finiteCoefficientSlice ℓ n U) ≃
      (Over.mk V.hom.left ⟶ AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme U.left (ULift.{u} (ZMod (ℓ ^ n)))) where
  toFun f := Over.homMk f.left.left (by
    exact congrArg (fun g : V.left ⟶ U => g.left) f.w)
  invFun g := Over.homMk (MorphismProperty.Over.homMk g.left (by
    change g.left ≫ (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme U.left (ULift.{u} (ZMod (ℓ ^ n)))).hom ≫ U.hom =
      V.left.hom
    rw [← Category.assoc, g.w]
    exact MorphismProperty.Over.w V.hom)) (by
      apply MorphismProperty.Over.Hom.ext
      exact g.w)
  left_inv f := by
    apply Over.OverMorphism.ext
    apply MorphismProperty.Over.Hom.ext
    rfl
  right_inv g := by
    apply Over.OverMorphism.ext
    rfl

/-- The coefficient sheaf restricted to a slice is represented by the actual finite constant scheme. -/
def Local.Construction.finiteCoefficientOnSliceRepresentable :
    ((Over.forget U).op ⋙ ((Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X).obj ⋙ forget Ab.{u + 1})).RepresentableBy
      (Local.Construction.finiteCoefficientSlice ℓ n U) where
  homEquiv {V} := (Local.Construction.finiteCoefficientSliceHomEquiv ℓ n U V).trans
    ((AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv U.left (ULift.{u} (ZMod (ℓ ^ n))) (Over.mk V.hom.left)).trans
      ((LocallyConstant.congrRight Equiv.ulift).trans
        (Finite.ConstantScheme.Construction.locallyConstantContinuousEquiv.trans Equiv.ulift.symm)))
  homEquiv_comp f g := by
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    rfl

variable {ℓ n U} (E : App.Construction.FiniteCoefficientExtension ℓ n X)

/-- Every local lift gives an actual finite étale representative of the torsor on that slice. -/
def App.Construction.FiniteCoefficientExtension.localRepresentative (s : E.Fiber U) :
    ((Over.forget U).op ⋙ E.fiberPresheaf).RepresentableBy (Local.Construction.finiteCoefficientSlice ℓ n U) :=
  (Local.Construction.finiteCoefficientOnSliceRepresentable ℓ n U).ofIso (E.trivialization U s)

/-- There is a covering sieve on which the actual torsor has the explicit finite étale representatives. -/
theorem App.Construction.FiniteCoefficientExtension.exists_covering_localRepresentatives :
    ∃ S : Sieve (⊤_ X.ProEt), S ∈ Scheme.ProEt.topology X (⊤_ X.ProEt) ∧
      ∀ (U : X.ProEt) (f : U ⟶ ⊤_ X.ProEt), S f →
        Nonempty (((Over.forget U).op ⋙ E.fiberPresheaf).RepresentableBy
          (Local.Construction.finiteCoefficientSlice ℓ n U)) := by
  refine ⟨Presheaf.imageSieve E.projection.hom
    (App.Construction.proEtIntegerLocalGenerator X (⊤_ X.ProEt)), E.fiber_locally_nonempty _, ?_⟩
  intro U f hf
  obtain ⟨s⟩ := E.fiber_nonempty_of_imageSieve f hf
  exact ⟨E.localRepresentative s⟩

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor
