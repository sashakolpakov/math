import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.ActionLoci
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.EndomorphismFamiliesId

/-! # Action Scheme -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.ActionScheme

noncomputable section

/-! Construction of the integral-action parameter scheme from the actual
relative endomorphism functor. Representability of that underlying Hom
functor is the separate Presentations step; the action scheme and universal action
are constructed here by finite equations. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

variable {S : Scheme.{u}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  {R : Type u} [CommRing R]

@[simp] theorem ringHomOfIntegralAction_ofRingHom (ρ : R →+* Finite.Actions.GroupEndRing A) :
    Finite.Actions.ringHomOfIntegralAction A (Finite.Actions.integralActionOfRingHom A ρ) = ρ := by
  apply RingHom.ext
  intro x
  apply Finite.Actions.GroupEndRing.ext
  rfl

@[simp] theorem integralActionOfRingHom_ofAction (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A) :
    Finite.Actions.integralActionOfRingHom A (Finite.Actions.ringHomOfIntegralAction A ρ) = ρ := by
  apply Finite.Actions.integralAction_ext
  intro x
  rfl

theorem ringHomOfIntegralAction_injective : Function.Injective
    (Finite.Actions.ringHomOfIntegralAction A : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A → R →+* Finite.Actions.GroupEndRing A) := by
  intro ρ σ h
  apply Finite.Actions.integralAction_ext
  intro x
  exact congrArg (Finite.Actions.GroupEndRing.hom A) (RingHom.congr_fun h x)

def restrictIntegralAction {T U : Over S}
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R (A.pullback U.hom)) (f : T ⟶ U) :
    AbelianModuli.ReferenceFamily.ActionData.IntegralAction R (A.pullback T.hom) :=
  Finite.Actions.integralActionOfRingHom (A.pullback T.hom)
    ((EndomorphismFamiliesId.EndomorphismFamilies.restrict A f).comp (Finite.Actions.ringHomOfIntegralAction (A.pullback U.hom) ρ))

@[simp] theorem restrictIntegralAction_ringHom {T U : Over S}
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R (A.pullback U.hom)) (f : T ⟶ U) :
    Finite.Actions.ringHomOfIntegralAction (A.pullback T.hom) (restrictIntegralAction A ρ f) =
      (EndomorphismFamiliesId.EndomorphismFamilies.restrict A f).comp (Finite.Actions.ringHomOfIntegralAction (A.pullback U.hom) ρ) :=
  ringHomOfIntegralAction_ofRingHom _ _

theorem restrictIntegralAction_id (T : Over S)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R (A.pullback T.hom)) :
    restrictIntegralAction A ρ (𝟙 T) = ρ := by
  apply ringHomOfIntegralAction_injective
  apply RingHom.ext
  intro x
  change EndomorphismFamiliesId.EndomorphismFamilies.restrict A (𝟙 T)
      (Finite.Actions.ringHomOfIntegralAction (A.pullback T.hom) ρ x) = _
  exact EndomorphismFamiliesId.EndomorphismFamilies.restrict_id A T _

theorem restrictIntegralAction_comp {T U V : Over S} (f : T ⟶ U) (h : U ⟶ V)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R (A.pullback V.hom)) :
    restrictIntegralAction A ρ (f ≫ h) =
      restrictIntegralAction A (restrictIntegralAction A ρ h) f := by
  apply ringHomOfIntegralAction_injective
  rw [restrictIntegralAction_ringHom, restrictIntegralAction_ringHom,
    restrictIntegralAction_ringHom]
  apply RingHom.ext
  intro x
  exact EndomorphismFamiliesId.EndomorphismFamilies.restrict_comp A f h _

variable (E : Type u) [Field E] [NumberField E]

/-- The integral action locus is a constructed closed subscheme of a
finite power of the relative endomorphism parameter scheme. It carries an
actual universal integral action and classifies all actions uniquely under
geometric restriction. -/
theorem exists_integral_action_parameter_scheme
    (H : Over S) [IsSeparated H.hom]
    (e : (EndomorphismFamiliesId.EndomorphismFamilies.endomorphismFunctor A ⋙ forget RingCat).RepresentableBy H) :
    ∃ (Z : Over S)
      (j : Z ⟶ ∏ᶜ fun _ : Fin (Module.finrank ℤ (NumberField.RingOfIntegers E)) => H),
      IsClosedImmersion j.left ∧
      ∃ ρZ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.pullback Z.hom),
        ∀ (T : Over S) (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.pullback T.hom)),
          ∃! f : T ⟶ Z, restrictIntegralAction A ρZ f = ρ := by
  let F := EndomorphismFamiliesId.EndomorphismFamilies.endomorphismFunctor A
  obtain ⟨Z, j, hj, rZ, _, hclass⟩ :=
    Finite.ActionLoci.FiniteActionLocus.exists_universal_action_scheme F H e (Finite.Actions.integralActionBasis E)
  let ρZ := Finite.Actions.integralActionOfRingHom (A.pullback Z.hom) rZ
  refine ⟨Z, j, hj, ρZ, ?_⟩
  intro T ρ
  obtain ⟨f, hf, huniq⟩ := hclass T (Finite.Actions.ringHomOfIntegralAction (A.pullback T.hom) ρ)
  have hiff (f : T ⟶ Z) : restrictIntegralAction A ρZ f = ρ ↔
      (F.map f.op).hom.comp rZ = Finite.Actions.ringHomOfIntegralAction (A.pullback T.hom) ρ := by
    rw [← (ringHomOfIntegralAction_injective (A.pullback T.hom)).eq_iff,
      restrictIntegralAction_ringHom]
    change (EndomorphismFamiliesId.EndomorphismFamilies.restrict A f).comp
        (Finite.Actions.ringHomOfIntegralAction (A.pullback Z.hom)
          (Finite.Actions.integralActionOfRingHom (A.pullback Z.hom) rZ)) = _ ↔ _
    exact (congrArg (fun q => (EndomorphismFamiliesId.EndomorphismFamilies.restrict A f).comp q =
        Finite.Actions.ringHomOfIntegralAction (A.pullback T.hom) ρ)
      (ringHomOfIntegralAction_ofRingHom (A.pullback Z.hom) rZ)).to_iff
  exact ⟨f, (hiff f).mpr hf, fun g hg => huniq g ((hiff g).mp hg)⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.ActionScheme
