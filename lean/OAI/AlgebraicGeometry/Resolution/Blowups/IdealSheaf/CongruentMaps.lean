import OAI.AlgebraicGeometry.Resolution.Blowups.ClosedCarrierCenters
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.OrderLocusPreservation

/-! # Congruent Maps -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.CongruentMaps.Construction

noncomputable section

/-! Intrinsic congruence of scheme maps on a closed subscheme preserves every ideal containing its defining ideal. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem idealSheaf_map_comap_subscheme_of_le {X : Scheme.{u}} (T I : X.IdealSheafData) (hTI : T ≤ I) :
    (I.comap T.subschemeι).map T.subschemeι = I := by
  let j := Scheme.IdealSheafData.inclusion hTI
  have he : j.ker.map T.subschemeι = I := by
    rw [Scheme.IdealSheafData.map_ker, Scheme.IdealSheafData.inclusion_subschemeι,
      Scheme.IdealSheafData.ker_subschemeι]
  calc
    (I.comap T.subschemeι).map T.subschemeι =
        ((j.ker.map T.subschemeι).comap T.subschemeι).map T.subschemeι := by rw [he]
    _ = j.ker.map T.subschemeι := congrArg (fun L => L.map T.subschemeι)
      (ClosedCarrierCenters.Construction.idealSheaf_closed_comap_map T.subschemeι j.ker)
    _ = I := he

theorem idealSheaf_eq_of_subscheme_comap {X : Scheme.{u}} (T I J : X.IdealSheafData)
    (hTI : T ≤ I) (hTJ : T ≤ J) (h : I.comap T.subschemeι = J.comap T.subschemeι) : I = J := by
  have he := congrArg (fun L => L.map T.subschemeι) h
  rwa [idealSheaf_map_comap_subscheme_of_le T I hTI, idealSheaf_map_comap_subscheme_of_le T J hTJ] at he

def IdealSheafCongruent {U X : Scheme.{u}} (a b : U ⟶ X) (T : X.IdealSheafData) : Prop :=
  T.comap a = T.comap b ∧ (T.comap a).subschemeι ≫ a = (T.comap a).subschemeι ≫ b

theorem IdealSheafCongruent.preservesIdeal {U X : Scheme.{u}} {a b : U ⟶ X} {T : X.IdealSheafData}
    (h : IdealSheafCongruent a b T) (I : X.IdealSheafData) (hTI : T ≤ I) : I.comap a = I.comap b := by
  apply idealSheaf_eq_of_subscheme_comap (T.comap a) _ _ (Scheme.IdealSheafData.comap_mono a hTI)
  · rw [h.1]
    exact Scheme.IdealSheafData.comap_mono b hTI
  · rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, h.2]

theorem IdealSheafCongruent.preserves_permissible_center
    {U X : Scheme} {a b : U ⟶ X} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J : X.IdealSheafData) (n : ℕ)
    (h : IdealSheafCongruent a b (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n)) (I : X.IdealSheafData)
    (hp : J ≤ I ^ (n + 1)) : I.comap a = I.comap b :=
  h.preservesIdeal I (Global.OrderLocusPreservation.Construction.global_tangent_le_permissible_center f J I n hp)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.CongruentMaps.Construction
