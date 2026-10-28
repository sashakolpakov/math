import OAI.NumberTheory.Quaternion.Arithmetic.PrimeMaskExponentials
import OAI.NumberTheory.Quaternion.Arithmetic.MatrixOpenness

/-! # Prime Block Decomposition -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.PrimeBlockDecomposition

noncomputable section

section

/-! Actual closed subgroups of finite products of local matrix points
split into their residue-characteristic blocks near the identity. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Operator
open IsDedekindDomain NormedSpace Set Filter _root_.Topology

variable {F : Type} [Field F] [NumberField F] {n : ℕ}
variable {ι : Type*} [Fintype ι]

local instance primeBlocksMatrixComplete (v : HeightOneSpectrum (𝓞 F)) :
    @CompleteSpace (Matrix (Fin n) (Fin n) (v.adicCompletion F))
      (inferInstance : NormedRing (Matrix (Fin n) (Fin n) (v.adicCompletion F))).toUniformSpace :=
  FiniteDimensional.complete (v.adicCompletion F) _

def finiteMatrixProductHom (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (v : ι → HeightOneSpectrum (𝓞 F)) :
    (∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i))) →* (∀ i, Matrix (Fin n) (Fin n) ((v i).adicCompletion F)) where
  toFun g i := MatrixOpenness.localMatrixMonoidHom G (v i) (g i)
  map_one' := by funext i; exact map_one _
  map_mul' g h := by funext i; exact map_mul _ _ _

def localPrimeBlock (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (v : ι → HeightOneSpectrum (𝓞 F)) (q : ℕ) :
    (∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i))) →* (∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i))) where
  toFun g i := if LocalCompletion.residuePrime (v i) = q then g i else 1
  map_one' := by funext i; split_ifs <;> rfl
  map_mul' g h := by
    funext i
    by_cases hq : LocalCompletion.residuePrime (v i) = q <;> simp [hq]

theorem localPrimeBlock_mem_of_small (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (v : ι → HeightOneSpectrum (𝓞 F))
    (H : Subgroup (∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i))))
    (hH : IsClosed (H : Set (∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i)))))
    {g : ∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i))} (hg : g ∈ H)
    (hsmall : ∀ i, MatrixOpenness.localMatrixMonoidHom G (v i) (g i) ∈
      SpanLocal.finiteLogDomain (v i) (Matrix (Fin n) (Fin n) ((v i).adicCompletion F))) (q : ℕ) :
    localPrimeBlock G v q g ∈ H := by
  let e := finiteMatrixProductHom G v
  have he : IsClosedEmbedding e := IsClosedEmbedding.piMap (fun i => IntegralCompact.localPoints_closedEmbedding G _)
  let HM := H.toSubmonoid.map e
  have hc : IsClosed (HM : Set (∀ i, Matrix (Fin n) (Fin n) ((v i).adicCompletion F))) :=
    he.isClosedMap _ hH
  let X := fun i => SpanLocal.finiteLocalLog (v i) (Matrix (Fin n) (Fin n) ((v i).adicCompletion F))
    (e g i)
  have hX (i : ι) : X i ∈ Metric.eball 0
      (expSeries ((v i).adicCompletion F) (Matrix (Fin n) (Fin n) ((v i).adicCompletion F))).radius :=
    (hsmall i).2
  have hex (i : ι) : exp (X i) = e g i := SpanLocal.exp_finiteLocalLog (v i) (hsmall i)
  have hexp : (fun i => exp (X i)) ∈ HM := by
    simp only [hex]
    exact ⟨g, hg, rfl⟩
  have hb := PrimeMaskExponentials.prime_mask_exp_mem_closed_submonoid v HM hc X hX hexp q
  have heq : (fun i => if LocalCompletion.residuePrime (v i) = q then exp (X i) else 1) =
      e (localPrimeBlock G v q g) := by
    funext i
    simp only [hex, e, finiteMatrixProductHom, MonoidHom.coe_mk, OneHom.coe_mk,
      localPrimeBlock]
    split_ifs <;> rfl
  have hb' : e (localPrimeBlock G v q g) ∈ HM := heq ▸ hb
  obtain ⟨a, ha, hea⟩ := hb'
  exact he.injective hea ▸ ha

theorem localPrimeBlock_eventually_mem (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (v : ι → HeightOneSpectrum (𝓞 F))
    (H : Subgroup (∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i))))
    (hH : IsClosed (H : Set (∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i))))) :
    ∀ᶠ g in 𝓝 (1 : ∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i))),
      g ∈ H → ∀ q, localPrimeBlock G v q g ∈ H := by
  have hnear : ∀ᶠ g in 𝓝 (1 : ∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i))),
      ∀ i, MatrixOpenness.localMatrixMonoidHom G (v i) (g i) ∈
        SpanLocal.finiteLogDomain (v i) (Matrix (Fin n) (Fin n) ((v i).adicCompletion F)) := by
    apply Filter.eventually_all.mpr
    intro i
    have ht := ((IntegralCompact.localPoints_closedEmbedding G (Sum.inr (v i))).continuous.comp
      (continuous_apply i)).tendsto (1 : ∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i)))
    exact ht (SpanLocal.finiteLogDomain_mem_nhds (v i) (Matrix (Fin n) (Fin n) ((v i).adicCompletion F)))
  filter_upwards [hnear] with g hg
  exact fun h q => localPrimeBlock_mem_of_small G v H hH h hg q

end

/-! Near the identity, membership in a closed local-product subgroup can
be checked separately in each residue-characteristic block. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain Set Filter _root_.Topology

variable {F : Type} [Field F] [NumberField F] {n : ℕ}
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem localPrimeBlock_prod_eq (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (v : ι → HeightOneSpectrum (𝓞 F)) (P : Finset ℕ)
    (hP : ∀ i, LocalCompletion.residuePrime (v i) ∈ P) (g : ∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i))) :
    (P.toList.map (fun q => localPrimeBlock G v q g)).prod = g := by
  funext i
  rw [Pi.list_prod_apply, List.map_map]
  change (P.toList.map (fun q => if LocalCompletion.residuePrime (v i) = q then g i else 1)).prod = g i
  have h := List.prod_map_eq_pow_single (LocalCompletion.residuePrime (v i))
    (fun q => if LocalCompletion.residuePrime (v i) = q then g i else 1)
    (l := P.toList) (fun q hq _ => ite_eq_right hq.symm)
  simpa only [ite_true, List.count_eq_one_of_mem P.nodup_toList (Finset.mem_toList.mpr (hP i)),
    pow_one] using h

omit [Fintype ι] in
theorem mem_of_localPrimeBlocks_mem (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (v : ι → HeightOneSpectrum (𝓞 F)) (P : Finset ℕ)
    (hP : ∀ i, LocalCompletion.residuePrime (v i) ∈ P)
    (H : Subgroup (∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i))))
    {g : ∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i))}
    (hg : ∀ q ∈ P, localPrimeBlock G v q g ∈ H) : g ∈ H := by
  rw [← localPrimeBlock_prod_eq G v P hP g]
  apply H.list_prod_mem
  intro x hx
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
  exact hg q (Finset.mem_toList.mp hq)

theorem localPrimeBlock_eventually_iff (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (v : ι → HeightOneSpectrum (𝓞 F)) (P : Finset ℕ)
    (hP : ∀ i, LocalCompletion.residuePrime (v i) ∈ P)
    (H : Subgroup (∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i))))
    (hH : IsClosed (H : Set (∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i))))) :
    ∀ᶠ g in 𝓝 (1 : ∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i))),
      g ∈ H ↔ ∀ q ∈ P, localPrimeBlock G v q g ∈ H := by
  filter_upwards [localPrimeBlock_eventually_mem G v H hH] with g hg
  exact ⟨fun h q _ => hg h q, mem_of_localPrimeBlocks_mem G v P hP H⟩

omit [Fintype ι] in
theorem local_subgroup_isOpen_of_primeBlock_neighborhoods (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (v : ι → HeightOneSpectrum (𝓞 F)) (P : Finset ℕ)
    (hP : ∀ i, LocalCompletion.residuePrime (v i) ∈ P)
    (H : Subgroup (∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i))))
    (hnear : ∀ q ∈ P, ∀ᶠ g in 𝓝 (1 : ∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i))),
      localPrimeBlock G v q g ∈ H) : IsOpen (H : Set (∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i)))) := by
  apply H.isOpen_of_mem_nhds (g := 1)
  have h := P.eventually_all.mpr hnear
  filter_upwards [h] with g hg
  exact mem_of_localPrimeBlocks_mem G v P hP H hg

end

end OAI.NumberTheory.Quaternion.Arithmetic.PrimeBlockDecomposition
