import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.BlowupChart
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlledTransformMap
import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.ChartOpenBaseChange

/-! # Chart Specified Map -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.ChartSpecifiedMap.Construction

noncomputable section

/-! Actual affine chart maps with the target center and exceptional generator named independently. -/

universe u

variable {R S : Type u} [CommRing R] [CommRing S]

def blowupChartMapTo (I : Ideal R) (a : I) (φ : R →+* S) (K : Ideal S) (hK : I.map φ = K)
    (b : K) (hb : b.val = φ a.val) : Charts.Construction.blowupChart I a →+* Charts.Construction.blowupChart K b := by
  subst K
  have he : b = ⟨φ a.val, Ideal.mem_map_of_mem φ a.property⟩ := Subtype.ext hb
  subst b
  exact ChartLift.Construction.blowupChartMap I φ a

theorem blowupChartMapTo_constants (I : Ideal R) (a : I) (φ : R →+* S) (K : Ideal S) (hK : I.map φ = K)
    (b : K) (hb : b.val = φ a.val) (r : R) :
    blowupChartMapTo I a φ K hK b hb (Charts.Construction.blowupChartConstants I a r) = Charts.Construction.blowupChartConstants K b (φ r) := by
  subst K
  have he : b = ⟨φ a.val, Ideal.mem_map_of_mem φ a.property⟩ := Subtype.ext hb
  subst b
  exact ChartLift.Construction.blowupChartMap_constants I φ a r

theorem blowupChartMapTo_ratio (I : Ideal R) (a : I) (φ : R →+* S) (K : Ideal S) (hK : I.map φ = K)
    (b : K) (hb : b.val = φ a.val) (z : I) (w : K) (hw : w.val = φ z.val) :
    blowupChartMapTo I a φ K hK b hb (ExceptionalIdeal.Construction.blowupChartRatio I a z) = ExceptionalIdeal.Construction.blowupChartRatio K b w := by
  subst K
  have he : b = ⟨φ a.val, Ideal.mem_map_of_mem φ a.property⟩ := Subtype.ext hb
  have hew : w = ⟨φ z.val, Ideal.mem_map_of_mem φ z.property⟩ := Subtype.ext hw
  subst b
  subst w
  exact Blowups.Etale.BlowupChart.Construction.blowupChartMap_ratio I φ a z

theorem blowupChartMapTo_etale (I : Ideal R) (a : I) (φ : R →+* S) (hφ : φ.Etale)
    (K : Ideal S) (hK : I.map φ = K) (b : K) (hb : b.val = φ a.val) :
    (blowupChartMapTo I a φ K hK b hb).Etale := by
  subst K
  have he : b = ⟨φ a.val, Ideal.mem_map_of_mem φ a.property⟩ := Subtype.ext hb
  subst b
  let : Algebra R S := φ.toAlgebra
  let : Algebra.Etale R S := hφ
  exact Blowups.Etale.BlowupChart.Construction.blowupChartMap_ringHom_etale I a

theorem blowupChartMapTo_controlledIdeal (I J : Ideal R) (a : I) (φ : R →+* S)
    (K : Ideal S) (hK : I.map φ = K) (b : K) (hb : b.val = φ a.val) (c : ℕ) (hp : J ≤ I ^ c) :
    (ControlledTransform.Construction.blowupControlledTransform I J c a).map (blowupChartMapTo I a φ K hK b hb) =
      ControlledTransform.Construction.blowupControlledTransform K (J.map φ) c b := by
  subst K
  have he : b = ⟨φ a.val, Ideal.mem_map_of_mem φ a.property⟩ := Subtype.ext hb
  subst b
  exact ControlledTransformMap.Construction.blowupChartMap_controlledIdeal I J a φ c hp

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

def blowupChartMapToAlgHom (k : Type u) [CommRing k] [Algebra k R] [Algebra k S]
    (I : Ideal R) (a : I) (φ : R →ₐ[k] S) (K : Ideal S) (hK : I.map φ.toRingHom = K)
    (b : K) (hb : b.val = φ a.val) : Charts.Construction.blowupChart I a →ₐ[k] Charts.Construction.blowupChart K b where
  toRingHom := blowupChartMapTo I a φ.toRingHom K hK b hb
  commutes' c := by
    change blowupChartMapTo I a φ.toRingHom K hK b hb (Charts.Construction.blowupChartConstants I a (algebraMap k R c)) =
      Charts.Construction.blowupChartConstants K b (algebraMap k S c)
    exact (blowupChartMapTo_constants I a φ.toRingHom K hK b hb _).trans
      (congrArg (Charts.Construction.blowupChartConstants K b) (φ.commutes c))

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.ChartSpecifiedMap.Construction
