import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.BlowupKernelSheaf
import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.Equivalence

/-! # Blowup Closed Kernel -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Affine.BlowupClosedKernel.Construction

noncomputable section

/-! The closed blowup kernel depends on the actual quotient ideal, independently of its presentation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem affineBlowupMapTo_ker_eq_map {R S : Type u} [CommRing R] [CommRing S]
    (I : Ideal R) (K : Ideal S) (φ : R →+* S) (h : I.map φ = K) :
    (Blowup.Functor.Construction.affineBlowupMapTo I K φ h).ker = (ReesMap.Construction.affineBlowupMap I φ).ker := by
  subst K
  rfl

theorem affineBlowupMap_ker_eq_quotient {R S : Type u} [CommRing R] [CommRing S]
    (I : Ideal R) (φ : R →+* S) (hφ : Function.Surjective φ) :
    (ReesMap.Construction.affineBlowupMap I φ).ker =
      (ReesMap.Construction.affineBlowupMap I (Ideal.Quotient.mk (RingHom.ker φ))).ker := by
  let ψ := Ideal.Quotient.mk (RingHom.ker φ)
  let e := RingHom.quotientKerEquivOfSurjective hφ
  have hf : e.toRingHom.comp ψ = φ := by
    ext r
    exact RingHom.quotientKerEquivOfSurjective_apply_mk hφ r
  have hmap : (I.map ψ).map e.toRingHom = I.map φ := by rw [Ideal.map_map, hf]
  have hmap' : I.map (e.toRingHom.comp ψ) = I.map φ := by rw [hf]
  let l := Blowup.Functor.Construction.affineBlowupMapTo (I.map ψ) (I.map φ) e.toRingHom hmap
  let : IsIso l := Blowup.Equivalence.Construction.affineBlowupMapTo_isIso_of_equiv _ _ e hmap
  have he := Blowup.Functor.Construction.affineBlowupMapTo_comp I (I.map ψ) (I.map φ) ψ e.toRingHom rfl hmap hmap'
  have hleft : Blowup.Functor.Construction.affineBlowupMapTo I (I.map φ) (e.toRingHom.comp ψ) hmap' =
      ReesMap.Construction.affineBlowupMap I φ := by
    simp only [hf]
    rfl
  rw [hleft] at he
  change ReesMap.Construction.affineBlowupMap I φ = l ≫ ReesMap.Construction.affineBlowupMap I ψ at he
  rw [he, Scheme.Hom.ker_comp_of_isIso]

theorem framed_closed_hypersurface_affineBlowup_ker
    {k R S ι : Type u} [CommRing k] [CommRing R] [CommRing S] [Algebra k R]
    [IsNoetherianRing R] [Algebra ℚ R] [DecidableEq ι]
    (I : Ideal R) (g : ι → I) (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (g j).val = if i = j then 1 else 0)
    (hgen : Ideal.span (Set.range (fun i => (g i).val)) = I) (j : ι)
    (φ : R →+* S) (hφ : Function.Surjective φ) (hker : RingHom.ker φ = Ideal.span {(g j).val}) :
    (ReesMap.Construction.affineBlowupMap I φ).ker = ControlledIdealNaturality.Construction.affineControlledIdealSheaf I (Ideal.span {(g j).val}) 1 := by
  rw [affineBlowupMap_ker_eq_quotient I φ hφ, hker]
  exact BlowupKernelSheaf.Construction.framed_hypersurface_affineBlowup_ker I g D hD hgen j

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Affine.BlowupClosedKernel.Construction
