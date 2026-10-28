import OAI.AlgebraicGeometry.PELModuli.CMPoints.LocalPadic

/-! # Coordinate Separation -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.CoordinateSeparation

noncomputable section

/-! Distinct Galois characters remain distinct modulo q away from a single
separability denominator of an integral primitive element. -/

open _root_.NumberField _root_.Polynomial

theorem residue_characters_injective_at_generator
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    {q : ℕ} [Fact q.Prime]
    (B : PowerBasis ℚ E) (hint : IsIntegral ℤ B.gen)
    (r : RingOfIntegers E →+* ZMod q)
    (hsep : ((minpoly ℤ (⟨B.gen, hint⟩ : RingOfIntegers E)).map
      (Int.castRingHom (ZMod q))).Separable) :
    Function.Injective (fun τ : Gal(E/ℚ) =>
      r (RingOfIntegers.mapRingHom τ.toRingHom ⟨B.gen, hint⟩)) := by
  classical
  let θ : RingOfIntegers E := ⟨B.gen, hint⟩
  let f : ℤ[X] := minpoly ℤ θ
  let P := f.map (algebraMap ℤ (RingOfIntegers E))
  have hm : P.Monic := (minpoly.monic θ.isIntegral).map _
  have hmap : P.map r = f.map (Int.castRingHom (ZMod q)) := by
    rw [Polynomial.map_map]
    congr 1
    ext n
    simp
  have hs : (P.map r).Separable := hmap.symm ▸ hsep
  have hn : (P.roots.map r).Nodup :=
    Multiset.nodup_of_le (Polynomial.map_roots_le (hm.map r).ne_zero)
      (Polynomial.nodup_roots hs)
  have hroot (τ : Gal(E/ℚ)) : RingOfIntegers.mapRingHom τ.toRingHom θ ∈ P.roots := by
    rw [Polynomial.mem_roots hm.ne_zero, Polynomial.IsRoot.def, Polynomial.eval_map]
    change aeval ((RingOfIntegers.mapRingHom τ.toRingHom).toIntAlgHom θ) f = 0
    rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  intro τ σ h
  have he := Multiset.inj_on_of_nodup_map hn _ (hroot τ) _ (hroot σ) h
  have he' : τ.toAlgHom = σ.toAlgHom := B.algHom_ext
    (congrArg (fun a : RingOfIntegers E => (a : E)) he)
  exact AlgEquiv.coe_toAlgHom_injective he'

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.CoordinateSeparation
