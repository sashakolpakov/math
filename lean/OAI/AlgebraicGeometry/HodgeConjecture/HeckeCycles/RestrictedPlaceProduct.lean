import OAI.RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits

/-! # Restricted Place Product -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.RestrictedPlaceProduct.CM

/-! Split a genuine restricted product into one local factor and the
subgroup whose component at that place is the identity. -/

open scoped Classical RestrictedProduct
open OAI.RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction
variable {I : Type*} {G : I → Type*} [∀ i, Group (G i)]
  (K : ∀ i, Subgroup (G i)) (v : I)

def evaluation : RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K →* G v := RestrictedProduct.evalMonoidHom G v

def away : Subgroup (RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K) := (evaluation K v).ker

def remove (g : RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K) : RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K := (RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace K v (g v))⁻¹ * g

theorem remove_same (g : RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K) : remove K v g v = 1 := by
  change (RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace K v (g v) v)⁻¹ * g v = 1
  rw [RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace_same, inv_mul_cancel]

theorem remove_other (g : RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K) {w : I} (hw : w ≠ v) : remove K v g w = g w := by
  change (RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace K v (g v) w)⁻¹ * g w = g w
  rw [RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace_other K hw, inv_one, one_mul]

def awayHom : RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K →* away K v where
  toFun g := ⟨remove K v g, remove_same K v g⟩
  map_one' := by
    apply Subtype.ext
    apply RestrictedProduct.ext
    intro w
    by_cases hw : w = v
    · subst w
      exact remove_same K v 1
    · exact remove_other K v 1 hw
  map_mul' g h := by
    apply Subtype.ext
    apply RestrictedProduct.ext
    intro w
    change remove K v (g * h) w = remove K v g w * remove K v h w
    by_cases hw : w = v
    · subst w
      rw [remove_same, remove_same, remove_same, one_mul]
    · rw [remove_other K v _ hw, remove_other K v _ hw, remove_other K v _ hw]
      rfl

theorem commute (a : G v) (b : away K v) : Commute (RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace K v a) b.val := by
  apply RestrictedProduct.ext
  intro w
  change RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace K v a w * b.val w = b.val w * RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace K v a w
  by_cases hw : w = v
  · subst w
    have hb : b.val v = 1 := b.property
    rw [hb, mul_one, one_mul]
  · rw [RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace_other K hw, one_mul, mul_one]

def assemble : G v × away K v →* RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K where
  toFun x := RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace K v x.1 * x.2.val
  map_one' := by
    change RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace K v 1 * 1 = 1
    rw [map_one, one_mul]
  map_mul' x y := by
    change RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace K v (x.1 * y.1) * (x.2.val * y.2.val) =
      (RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace K v x.1 * x.2.val) * (RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace K v y.1 * y.2.val)
    rw [map_mul]
    exact (commute K v y.1 x.2).mul_mul_mul_comm _ _

theorem assemble_split (g : RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K) : assemble K v (g v, awayHom K v g) = g := by
  change RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace K v (g v) * ((RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace K v (g v))⁻¹ * g) = g
  rw [← mul_assoc, mul_inv_cancel, one_mul]

theorem split_assemble (a : G v) (b : away K v) :
    ((assemble K v (a, b)) v, awayHom K v (assemble K v (a, b))) = (a, b) := by
  apply Prod.ext
  · change RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace K v a v * b.val v = a
    have hb : b.val v = 1 := b.property
    rw [RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace_same, hb, mul_one]
  · apply Subtype.ext
    apply RestrictedProduct.ext
    intro w
    change remove K v (assemble K v (a, b)) w = b.val w
    by_cases hw : w = v
    · subst w
      rw [remove_same]
      exact b.property.symm
    · rw [remove_other K v _ hw]
      change RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace K v a w * b.val w = b.val w
      rw [RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace_other K hw, one_mul]

def equivalence : G v × away K v ≃* RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K where
  toFun := assemble K v
  invFun g := (g v, awayHom K v g)
  left_inv x := split_assemble K v x.1 x.2
  right_inv := assemble_split K v
  map_mul' := (assemble K v).map_mul

def transport {H : Type*} [Group H] (e : G v ≃* H) : H × away K v ≃* RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K :=
  (MulEquiv.prodCongr e.symm (MulEquiv.refl _)).trans (equivalence K v)

theorem transport_split {H : Type*} [Group H] (e : G v ≃* H) (g : RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K) :
    transport K v e (e (g v), awayHom K v g) = g := by
  change assemble K v (e.symm (e (g v)), awayHom K v g) = g
  rw [MulEquiv.symm_apply_apply]
  exact assemble_split K v g

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.RestrictedPlaceProduct.CM

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.RestrictedPlaceProduct.CM.Topology

/-! The local/away restricted-product decomposition is a homeomorphism. -/

open scoped Classical RestrictedProduct
open OAI.RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction
open _root_.Topology
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.RestrictedPlaceProduct.CM
variable {I : Type*} {G : I → Type*} [∀ i, Group (G i)]
  [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]
  (K : ∀ i, Subgroup (G i)) [Fact (∀ i, IsOpen (K i : Set (G i)))] (v : I)

theorem away_continuous : Continuous (awayHom K v) := by
  apply Continuous.subtype_mk
  exact ((RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace_continuous K v).comp (RestrictedProduct.continuous_eval v)).inv.mul continuous_id

theorem assemble_continuous : Continuous (assemble K v) :=
  ((RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace_continuous K v).comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd)

def homeomorphism : G v × away K v ≃ₜ RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K where
  toEquiv := (equivalence K v).toEquiv
  continuous_toFun := assemble_continuous K v
  continuous_invFun := (RestrictedProduct.continuous_eval v).prodMk (away_continuous K v)

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.RestrictedPlaceProduct.CM.Topology

end

end OAI
