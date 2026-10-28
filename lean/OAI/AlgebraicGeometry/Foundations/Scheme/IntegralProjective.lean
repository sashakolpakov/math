import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveTransport
import Mathlib.AlgebraicGeometry.Properties

/-! # Integral Projective -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective

noncomputable section

/-!
# Integral smooth projective complex varieties

This file restricts actual smooth projective presentations to carriers satisfying
mathlib's `IsIntegral`. It therefore makes the usual irreducibility and
nonemptiness convention for a variety explicit, rather than identifying the
raw possibly disconnected presentation type with that convention.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- A smooth projective complex presentation whose actual scheme is integral. -/
abbrev IntegralProjectiveVariety :=
  {P : SmoothProjective.SmoothProjectivePresentation // IsIntegral P.carrier}

namespace IntegralProjectiveVariety

/-- Forget only the integral-carrier condition. -/
abbrev presentation (V : IntegralProjectiveVariety) : SmoothProjective.SmoothProjectivePresentation := V.val

/-- The underlying actual scheme. -/
abbrev carrier (V : IntegralProjectiveVariety) : Scheme := V.presentation.carrier

/-- The actual morphism specifying the complex base. -/
abbrev structureMap (V : IntegralProjectiveVariety) : V.carrier ⟶ ProjectiveSpace.complexBase :=
  V.presentation.structureMap

/-- The ambient dimension of the chosen projective embedding. -/
abbrev ambientDimension (V : IntegralProjectiveVariety) : ℕ :=
  V.presentation.ambientDimension

/-- The actual closed projective embedding. -/
abbrev embedding (V : IntegralProjectiveVariety) :
    V.carrier ⟶ ProjectiveSpace.projectiveSpace V.ambientDimension := V.presentation.embedding

instance (V : IntegralProjectiveVariety) : IsIntegral V.carrier := V.property

instance (V : IntegralProjectiveVariety) : Smooth V.structureMap := V.presentation.smooth

instance (V : IntegralProjectiveVariety) : IsClosedImmersion V.embedding :=
  V.presentation.projective.closedImmersion

/-- Integral varieties are nonempty in mathlib's actual scheme topology. -/
theorem carrier_nonempty (V : IntegralProjectiveVariety) : Nonempty V.carrier :=
  inferInstance

/-- Irreducibility follows from the native integral-scheme condition. -/
theorem carrier_irreducible (V : IntegralProjectiveVariety) :
    IrreducibleSpace V.carrier := inferInstance

/-- Reducedness follows from the native integral-scheme condition. -/
theorem carrier_reduced (V : IntegralProjectiveVariety) :
    IsReduced V.carrier := inferInstance

/-- The associated complex scheme as an object over the base. -/
abbrev toOver (V : IntegralProjectiveVariety) : Over ProjectiveSpace.complexBase := V.presentation.toOver

/-- The chosen embedding is over the specified complex base. -/
@[reassoc]
theorem embedding_over (V : IntegralProjectiveVariety) :
    V.embedding ≫ ProjectiveSpace.projectiveSpaceToBase V.ambientDimension = V.structureMap :=
  V.presentation.embedding_over

/-- Every bundled variety has an actual closed projective embedding. -/
theorem exists_closedImmersion (V : IntegralProjectiveVariety) :
    ∃ (n : ℕ) (i : V.carrier ⟶ ProjectiveSpace.projectiveSpace n),
      IsClosedImmersion i ∧ i ≫ ProjectiveSpace.projectiveSpaceToBase n = V.structureMap :=
  SmoothProjective.ProjectivePresentation.nonempty_iff.mp ⟨V.presentation.projective⟩

/-- Construct the bundle from exactly the standard algebraic conditions. -/
def ofClosedImmersion {X : Scheme} (f : X ⟶ ProjectiveSpace.complexBase)
    (n : ℕ) (i : X ⟶ ProjectiveSpace.projectiveSpace n) (hi : IsClosedImmersion i)
    (hif : i ≫ ProjectiveSpace.projectiveSpaceToBase n = f) (hf : Smooth f) (hX : IsIntegral X) :
    IntegralProjectiveVariety :=
  ⟨{ carrier := X
     structureMap := f
     projective := ⟨n, i, hi, hif⟩
     smooth := hf }, hX⟩

@[simp]
theorem ofClosedImmersion_carrier {X : Scheme} (f : X ⟶ ProjectiveSpace.complexBase)
    (n : ℕ) (i : X ⟶ ProjectiveSpace.projectiveSpace n) (hi : IsClosedImmersion i)
    (hif : i ≫ ProjectiveSpace.projectiveSpaceToBase n = f) (hf : Smooth f) (hX : IsIntegral X) :
    (ofClosedImmersion f n i hi hif hf hX).carrier = X := rfl

@[simp]
theorem ofClosedImmersion_structureMap {X : Scheme} (f : X ⟶ ProjectiveSpace.complexBase)
    (n : ℕ) (i : X ⟶ ProjectiveSpace.projectiveSpace n) (hi : IsClosedImmersion i)
    (hif : i ≫ ProjectiveSpace.projectiveSpaceToBase n = f) (hf : Smooth f) (hX : IsIntegral X) :
    (ofClosedImmersion f n i hi hif hf hX).structureMap = f := rfl

/-- Integrality as well as the chosen smooth projective presentation transports
along an actual scheme isomorphism. -/
def transportIso (V : IntegralProjectiveVariety) {Y : Scheme}
    (e : Y ≅ V.carrier) : IntegralProjectiveVariety :=
  ⟨V.presentation.transportIso e, by
    change IsIntegral Y
    exact IsIntegral.of_isIso e.inv⟩

@[simp]
theorem transportIso_structureMap (V : IntegralProjectiveVariety) {Y : Scheme}
    (e : Y ≅ V.carrier) :
    (V.transportIso e).structureMap = e.hom ≫ V.structureMap := rfl

/-- The transported object is genuinely isomorphic over `Spec ℂ`. -/
def transportIso_overIso (V : IntegralProjectiveVariety) {Y : Scheme}
    (e : Y ≅ V.carrier) : (V.transportIso e).toOver ≅ V.toOver :=
  V.presentation.transportIso_overIso e

/-- Exact coverage, up to isomorphism over the complex base, by the integral
smooth projective presentation type. No disconnected presentation is identified
with an irreducible variety in this statement. -/
theorem exists_overIso_iff (X : Scheme) (f : X ⟶ ProjectiveSpace.complexBase) :
    (∃ (V : IntegralProjectiveVariety) (e : X ≅ V.carrier),
      e.hom ≫ V.structureMap = f) ↔
    IsIntegral X ∧ Smooth f ∧
      ∃ (n : ℕ) (i : X ⟶ ProjectiveSpace.projectiveSpace n),
        IsClosedImmersion i ∧ i ≫ ProjectiveSpace.projectiveSpaceToBase n = f := by
  constructor
  · rintro ⟨V, e, he⟩
    have hX : IsIntegral X := IsIntegral.of_isIso e.inv
    have hf' : Smooth (e.hom ≫ V.structureMap) := inferInstance
    have hf : Smooth f := he ▸ hf'
    refine ⟨hX, hf, V.ambientDimension, e.hom ≫ V.embedding, inferInstance, ?_⟩
    rw [Category.assoc, V.embedding_over, he]
  · rintro ⟨hX, hf, n, i, hi, hif⟩
    let V := ofClosedImmersion f n i hi hif hf hX
    refine ⟨V, Iso.refl X, ?_⟩
    change (𝟙 X) ≫ f = f
    simp

end IntegralProjectiveVariety

end

end OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective
