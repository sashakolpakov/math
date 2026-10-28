import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.RelativeIso
import Mathlib.RingTheory.RingHom.Flat

/-! # Product Flatness Transport -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ProductFlatnessTransport

noncomputable section

/-! Flatness of the actual product projections is independent of the chosen product cone. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)}

theorem iso {U V : BigCrystallineSite.Object p B J δ f} (e : U ≅ V) : e.hom.ringMap.toRingHom.Flat :=
  RingHom.Flat.of_bijective (RelativeIso.ringEquiv e).bijective

theorem relative {U V T : BigCrystallineSite.Object p B J δ f} (α : U ⟶ T) (β : V ⟶ T) (e : U ≅ V)
    (he : e.hom ≫ β = α) (hβ : β.ringMap.toRingHom.Flat) : α.ringMap.toRingHom.Flat := by
  have h := hβ.comp (iso e)
  change (e.hom ≫ β).ringMap.toRingHom.Flat at h
  exact he ▸ h

theorem fst {U V : BigCrystallineSite.Object p B J δ f} (P Q : BinaryFan U V) (hP : IsLimit P) (hQ : IsLimit Q)
    (hQflat : Q.fst.ringMap.toRingHom.Flat) : P.fst.ringMap.toRingHom.Flat :=
  relative P.fst Q.fst (hP.conePointUniqueUpToIso hQ)
    (hP.conePointUniqueUpToIso_hom_comp hQ ⟨WalkingPair.left⟩) hQflat

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ProductFlatnessTransport
