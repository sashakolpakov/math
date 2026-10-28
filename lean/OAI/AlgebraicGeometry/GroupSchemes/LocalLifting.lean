import OAI.AlgebraicGeometry.GroupSchemes.LocalSurjectivity
import OAI.AlgebraicGeometry.GroupSchemes.Surjective
import OAI.AlgebraicGeometry.GroupSchemes.DualMaps
import OAI.AlgebraicGeometry.GroupSchemes.LocalObstruction

/-! # Local Lifting -/

namespace OAI.AlgebraicGeometry.GroupSchemes.LocalLifting.FiniteEtaleV

noncomputable section

/-! Lift surjectivity of Verschiebung through a quotient whose kernel lies in m². -/

open OAI.AlgebraicGeometry.GroupSchemes.Verschiebung.FiniteEtale OAI.AlgebraicGeometry.GroupSchemes.Surjective.FiniteEtaleV OAI.AlgebraicGeometry.GroupSchemes.LocalObstruction.FiniteEtale

universe u
variable (k A B : Type u) [Field k] [CommRing A] [CommRing B]
  [HopfAlgebra k A] [HopfAlgebra k B] [Coalgebra.IsCocomm k A] [Coalgebra.IsCocomm k B]
  [Module.Finite k A] [Module.Finite k B]
variable (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]

omit [CommRing B] [HopfAlgebra k B] [Coalgebra.IsCocomm k B] [Module.Finite k B]
  [Fact p.Prime] [CharP k p] [PerfectRing k p] [Coalgebra.IsCocomm k A] [Module.Finite k A] in
/-- In a local augmented algebra, the augmentation ideal is the maximal ideal. -/
theorem augmentation_eq_maximal [IsLocalRing A] :
    LocalObstruction.FiniteEtale.augmentationIdeal k A = IsLocalRing.maximalIdeal A := by
  apply IsLocalRing.eq_maximalIdeal
  apply RingHom.ker_isMaximal_of_surjective (Bialgebra.counitAlgHom k A).toRingHom
  intro c
  exact ⟨algebraMap k A c, by simp⟩

/-- Surjective Verschiebung on the quotient lifts to the local algebra if the kernel lies in m². -/
theorem surjective_of_quotient [IsLocalRing A] (q : A →ₐc[k] B)
    (hq : Function.Surjective q)
    (hker : RingHom.ker q.toAlgHom.toRingHom ≤ LocalObstruction.FiniteEtale.augmentationIdeal k A ^ 2)
    (hVB : Function.Surjective (Verschiebung.FiniteEtale.verschiebungFun p k B)) :
    Function.Surjective (Verschiebung.FiniteEtale.verschiebungFun p k A) := by
  have : IsNoetherianRing A := IsNoetherianRing.of_finite k A
  change Function.Surjective (Verschiebung.FiniteEtale.verschiebungRingHom p k A)
  apply LocalSurjectivity.FiniteEtale.surjective_of_cotangent
    (Verschiebung.FiniteEtale.verschiebungRingHom p k A) (GroupSchemes.Surjective.FiniteEtaleV.verschiebung_finite k A p)
  · rw [← augmentation_eq_maximal k A]
    apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    change Coalgebra.counit (R := k) x = 0 at hx
    change Coalgebra.counit (R := k) (Verschiebung.FiniteEtale.verschiebungFun p k A x) = 0
    rw [GroupSchemes.Surjective.FiniteEtaleV.counit_verschiebung, hx, map_zero]
  · rw [← augmentation_eq_maximal k A]
    intro x hx
    change Coalgebra.counit (R := k) x = 0 at hx
    obtain ⟨b, hb⟩ := hVB (q x)
    have hbaug : Coalgebra.counit (R := k) b = 0 := by
      apply (frobeniusEquiv k p).symm.injective
      rw [← GroupSchemes.Surjective.FiniteEtaleV.counit_verschiebung k B p, hb, CoalgHomClass.counit_comp_apply, hx, map_zero]
    obtain ⟨a, ha⟩ := hq b
    have haaug : a ∈ LocalObstruction.FiniteEtale.augmentationIdeal k A := by
      change Coalgebra.counit (R := k) a = 0
      rw [← CoalgHomClass.counit_comp_apply q a, ha, hbaug]
    have hrem : x - Verschiebung.FiniteEtale.verschiebungFun p k A a ∈ LocalObstruction.FiniteEtale.augmentationIdeal k A ^ 2 := by
      apply hker
      change q (x - Verschiebung.FiniteEtale.verschiebungFun p k A a) = 0
      rw [map_sub]
      have hn := DualMaps.FiniteEtale.verschiebung_natural k p q.toCoalgHom a
      change q (Verschiebung.FiniteEtale.verschiebungFun p k A a) = Verschiebung.FiniteEtale.verschiebungFun p k B (q a) at hn
      rw [hn, ha, hb, sub_self]
    exact Submodule.mem_sup.mpr ⟨Verschiebung.FiniteEtale.verschiebungFun p k A a,
      Ideal.mem_map_of_mem _ haaug, x - Verschiebung.FiniteEtale.verschiebungFun p k A a, hrem, by abel⟩
  · intro x
    refine ⟨algebraMap k A ((frobeniusEquiv k p) (Coalgebra.counit (R := k) x)), ?_⟩
    rw [← augmentation_eq_maximal k A]
    change Coalgebra.counit (R := k) (x - _) = 0
    rw [GroupSchemes.Surjective.FiniteEtaleV.verschiebung_scalars, RingEquiv.symm_apply_apply]
    simp

omit [CommRing B] [HopfAlgebra k B] [Coalgebra.IsCocomm k B] [Module.Finite k B] in
/-- Multiplication by p has zero linear term at the identity in characteristic p. -/
theorem multiplicationKernel_le_square :
    LocalObstruction.FiniteEtale.multiplicationKernelIdeal k p A ≤ LocalObstruction.FiniteEtale.augmentationIdeal k A ^ 2 := by
  apply Ideal.span_le.mpr
  rintro _ ⟨x, hx, rfl⟩
  change ((WithConv.toConv (LinearMap.id : A →ₗ[k] A)) ^ p) x ∈ LocalObstruction.FiniteEtale.augmentationIdeal k A ^ 2
  have hV : Verschiebung.FiniteEtale.verschiebungFun p k A x ∈ LocalObstruction.FiniteEtale.augmentationIdeal k A := by
    change Coalgebra.counit (R := k) x = 0 at hx
    change Coalgebra.counit (R := k) (Verschiebung.FiniteEtale.verschiebungFun p k A x) = 0
    rw [GroupSchemes.Surjective.FiniteEtaleV.counit_verschiebung, hx, map_zero]
  have hmem := (Ideal.pow_le_pow_right (Fact.out : p.Prime).two_le) (Ideal.pow_mem_pow hV p)
  exact (congrArg (fun z => z ∈ LocalObstruction.FiniteEtale.augmentationIdeal k A ^ 2)
    (Verschiebung.FiniteEtale.frobenius_verschiebung p k A x)).mp hmem

end

end OAI.AlgebraicGeometry.GroupSchemes.LocalLifting.FiniteEtaleV
