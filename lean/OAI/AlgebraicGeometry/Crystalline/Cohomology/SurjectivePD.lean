import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.FormSurjective

/-! # Surjective PD -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.SurjectivePD.SurjectivePDDerivation

noncomputable section

/-! # The divided-power derivation rule descends along a surjective PD map -/

universe u

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (I : Ideal A) (J : Ideal B)
  (δ : DividedPowers I) (ε : DividedPowers J) (q : A →ₐ[R] B)
  (hq : Function.Surjective q) (hI : I.map q.toRingHom = J)
  (hPD : DividedPowers.IsDPMorphism δ ε q.toRingHom)
  (DA : Derivation R A A) (DB : Derivation R B B)
  (hD : ∀ n a, a ∈ I → DA (δ.dpow (n + 1) a) = δ.dpow n a * DA a)
  (hc : ∀ a, DB (q a) = q (DA a))

include hq hI hPD hD hc in
theorem dpow (n : ℕ) (b : B) (hb : b ∈ J) : DB (ε.dpow (n + 1) b) = ε.dpow n b * DB b := by
  rw [← hI] at hb
  obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective q.toRingHom hq).mp hb
  change DB (ε.dpow (n + 1) (q a)) = ε.dpow n (q a) * DB (q a)
  exact (congrArg DB (hPD.map_dpow ha).symm).trans ((hc (δ.dpow (n + 1) a)).trans
    ((congrArg q (hD n a ha)).trans ((q.map_mul _ _).trans
      ((congrArg (fun z => z * q (DA a)) (hPD.map_dpow (n := n) ha)).trans
        (congrArg (fun z => ε.dpow n (q a) * z) (hc a).symm)))))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.SurjectivePD.SurjectivePDDerivation
