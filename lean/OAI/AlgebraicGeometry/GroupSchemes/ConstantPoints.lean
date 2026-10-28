import Mathlib

/-! # Constant Points -/

namespace OAI.AlgebraicGeometry.GroupSchemes.ConstantPoints.FiniteEtale

noncomputable section

/-! Finite constant schemes on every affine algebra, using clopen partitions and idempotents. -/

open _root_.TopologicalSpace

universe u v
variable {R : Type u} [CommRing R]
variable {ι : Type v} [Fintype ι]

/-- A complete orthogonal idempotent family selects exactly one member at every prime. -/
theorem existsUnique_index {e : ι → R} (he : CompleteOrthogonalIdempotents e)
    (P : PrimeSpectrum R) : ∃! i, e i ∉ P.asIdeal := by
  have hex : ∃ i, e i ∉ P.asIdeal := by
    by_contra h
    push Not at h
    have hs : ∑ i, e i ∈ P.asIdeal := Ideal.sum_mem _ fun i _ => h i
    rw [he.complete] at hs
    exact P.isPrime.one_notMem hs
  obtain ⟨i, hi⟩ := hex
  refine ⟨i, hi, ?_⟩
  intro j hj
  by_contra hji
  have hz : e j * e i ∈ P.asIdeal := (he.ortho hji).symm ▸ P.asIdeal.zero_mem
  exact hi ((P.isPrime.mem_or_mem hz).resolve_left hj)

/-- The index chosen by a complete orthogonal idempotent family. -/
def partitionIndex {e : ι → R} (he : CompleteOrthogonalIdempotents e)
    (P : PrimeSpectrum R) : ι := Classical.choose (existsUnique_index he P)

theorem partitionIndex_eq_iff {e : ι → R} (he : CompleteOrthogonalIdempotents e)
    (P : PrimeSpectrum R) (i : ι) : partitionIndex he P = i ↔ e i ∉ P.asIdeal := by
  have h := Classical.choose_spec (existsUnique_index he P)
  exact ⟨fun hi => hi ▸ h.1, fun hi => (h.2 i hi).symm⟩

/-- The selected index is locally constant, even when the affine ring is nonreduced. -/
def partitionFunction {e : ι → R} (he : CompleteOrthogonalIdempotents e) :
    LocallyConstant (PrimeSpectrum R) ι where
  toFun := partitionIndex he
  isLocallyConstant := by
    apply IsLocallyConstant.iff_isOpen_fiber.mpr
    intro i
    change IsOpen {P | partitionIndex he P = i}
    have hset : {P | partitionIndex he P = i} = (PrimeSpectrum.basicOpen (e i) : Set _) := by
      ext P
      exact partitionIndex_eq_iff he P i
    rw [hset]
    exact (PrimeSpectrum.basicOpen (e i)).isOpen

/-- The clopen fiber of a locally constant finite-index map. -/
def fiberClopen (f : LocallyConstant (PrimeSpectrum R) ι) (i : ι) : Clopens (PrimeSpectrum R) :=
  ⟨{P | f P = i}, f.isLocallyConstant.isClopen_fiber i⟩

/-- The unique idempotent cutting out a clopen fiber. -/
def fiberIdempotent (f : LocallyConstant (PrimeSpectrum R) ι) (i : ι) : R :=
  (PrimeSpectrum.isIdempotentElemEquivClopens.symm (fiberClopen f i)).val

omit [Fintype ι] in
theorem fiberIdempotent_idem (f : LocallyConstant (PrimeSpectrum R) ι) (i : ι) :
    IsIdempotentElem (fiberIdempotent f i) :=
  (PrimeSpectrum.isIdempotentElemEquivClopens.symm (fiberClopen f i)).property

omit [Fintype ι] in
theorem fiberIdempotent_basicOpen (f : LocallyConstant (PrimeSpectrum R) ι) (i : ι) :
    PrimeSpectrum.basicOpen (fiberIdempotent f i) = (fiberClopen f i).toOpens :=
  PrimeSpectrum.basicOpen_isIdempotentElemEquivClopens_symm _

omit [Fintype ι] in
theorem fiberIdempotent_ortho (f : LocallyConstant (PrimeSpectrum R) ι) :
    OrthogonalIdempotents (fiberIdempotent f) := by
  refine ⟨fiberIdempotent_idem f, ?_⟩
  intro i j hij
  apply PrimeSpectrum.basicOpen_injOn_isIdempotentElem
    ((fiberIdempotent_idem f i).mul (fiberIdempotent_idem f j)) IsIdempotentElem.zero
  rw [PrimeSpectrum.basicOpen_mul, fiberIdempotent_basicOpen, fiberIdempotent_basicOpen,
    PrimeSpectrum.basicOpen_zero]
  ext P
  change (f P = i ∧ f P = j) ↔ False
  exact ⟨fun h => hij (h.1.symm.trans h.2), False.elim⟩

/-- The clopen fibers give a complete orthogonal idempotent family. -/
theorem fiberIdempotent_complete (f : LocallyConstant (PrimeSpectrum R) ι) :
    CompleteOrthogonalIdempotents (fiberIdempotent f) := by
  classical
  refine ⟨fiberIdempotent_ortho f, ?_⟩
  apply PrimeSpectrum.basicOpen_injOn_isIdempotentElem
    (fiberIdempotent_ortho f).isIdempotentElem_sum IsIdempotentElem.one
  ext P
  change (∑ i, fiberIdempotent f i) ∉ P.asIdeal ↔ (1 : R) ∉ P.asIdeal
  refine ⟨fun _ => P.isPrime.one_notMem, fun _ hsum => ?_⟩
  have hi : fiberIdempotent f (f P) ∉ P.asIdeal := by
    change P ∈ PrimeSpectrum.basicOpen (fiberIdempotent f (f P))
    rw [fiberIdempotent_basicOpen]
    rfl
  apply hi
  rw [← (fiberIdempotent_ortho f).mul_sum_of_mem (Finset.mem_univ (f P))]
  exact P.asIdeal.mul_mem_left _ hsum

/-- Recovering the clopen fibers of a partition recovers its idempotents. -/
theorem fiberIdempotent_partitionFunction {e : ι → R}
    (he : CompleteOrthogonalIdempotents e) (i : ι) :
    fiberIdempotent (partitionFunction he) i = e i := by
  apply PrimeSpectrum.basicOpen_injOn_isIdempotentElem
    (fiberIdempotent_idem _ _) (he.idem i)
  rw [fiberIdempotent_basicOpen]
  ext P
  exact partitionIndex_eq_iff he P i

variable (k : Type*) [CommRing k] [Algebra k R]

/-- A complete orthogonal partition defines evaluation of a finite product algebra. -/
def partitionAlgHom {e : ι → R} (he : CompleteOrthogonalIdempotents e) :
    (ι → k) →ₐ[k] R where
  toFun a := ∑ i, algebraMap k R (a i) * e i
  map_one' := by simpa only [Pi.one_apply, map_one, one_mul] using he.complete
  map_zero' := by simp
  map_add' a b := by simp [add_mul, Finset.sum_add_distrib]
  map_mul' a b := by
    classical
    simp only [Pi.mul_apply, map_mul]
    symm
    calc
      (∑ i, algebraMap k R (a i) * e i) * (∑ j, algebraMap k R (b j) * e j) =
          ∑ i, ∑ j, (algebraMap k R (a i) * algebraMap k R (b j)) * (e i * e j) := by
        rw [Finset.sum_mul]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = ∑ i, algebraMap k R (a i) * algebraMap k R (b i) * e i := by
        simp only [he.mul_eq, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  commutes' c := by
    change (∑ i, algebraMap k R c * e i) = _
    rw [← Finset.mul_sum, he.complete, mul_one]

theorem partitionAlgHom_single {e : ι → R} (he : CompleteOrthogonalIdempotents e)
    [DecidableEq ι] (i : ι) : partitionAlgHom k he (Pi.single i 1) = e i := by
  simp [partitionAlgHom, Pi.single_apply]

/-- An algebra map from a finite product defines a complete orthogonal partition. -/
theorem algHom_partition [DecidableEq ι] (f : (ι → k) →ₐ[k] R) :
    CompleteOrthogonalIdempotents (fun i => f (Pi.single i 1)) :=
  (CompleteOrthogonalIdempotents.single (fun _ : ι => k)).map f.toRingHom

/-- Maps from a finite product algebra are determined by its coordinate idempotents. -/
theorem algHom_ext_single [DecidableEq ι] {f g : (ι → k) →ₐ[k] R}
    (h : ∀ i, f (Pi.single i 1) = g (Pi.single i 1)) : f = g := by
  apply AlgHom.toLinearMap_injective
  apply (Pi.basisFun k ι).ext
  intro i
  change f ((Pi.basisFun k ι) i) = g ((Pi.basisFun k ι) i)
  rw [Pi.basisFun_apply]
  exact h i

/-- Points of a finite constant affine scheme are locally constant functions on the spectrum. -/
def constantPointsEquiv : ((ι → k) →ₐ[k] R) ≃ LocallyConstant (PrimeSpectrum R) ι := by
  classical
  exact {
    toFun := fun f => partitionFunction (algHom_partition k f)
    invFun := fun f => partitionAlgHom k (fiberIdempotent_complete f)
    left_inv := fun f => by
      apply algHom_ext_single k
      intro i
      rw [partitionAlgHom_single, fiberIdempotent_partitionFunction]
    right_inv := fun f => by
      ext P
      apply (partitionIndex_eq_iff (algHom_partition k
        (partitionAlgHom k (fiberIdempotent_complete f))) P (f P)).mpr
      rw [partitionAlgHom_single]
      change P ∈ PrimeSpectrum.basicOpen (fiberIdempotent f (f P))
      rw [fiberIdempotent_basicOpen]
      rfl }

/-- The locally constant value is characterized by the corresponding idempotent at the prime. -/
theorem constantPointsEquiv_eq_iff (f : (ι → k) →ₐ[k] R)
    (P : PrimeSpectrum R) (i : ι) :
    letI : DecidableEq ι := Classical.decEq ι
    constantPointsEquiv k f P = i ↔ f (Pi.single i 1) ∉ P.asIdeal := by
  classical
  change partitionIndex (algHom_partition k f) P = i ↔ _
  exact partitionIndex_eq_iff (algHom_partition k f) P i

/-- The finite-constant-scheme equivalence is natural in arbitrary test algebras. -/
theorem constantPointsEquiv_naturality {S : Type*} [CommRing S] [Algebra k S]
    (a : R →ₐ[k] S) (f : (ι → k) →ₐ[k] R) :
    constantPointsEquiv k (a.comp f) =
      (constantPointsEquiv k f).comap
        ⟨PrimeSpectrum.comap a.toRingHom, PrimeSpectrum.continuous_comap _⟩ := by
  classical
  ext P
  apply (constantPointsEquiv_eq_iff k (a.comp f) P _).mpr
  have h := (constantPointsEquiv_eq_iff k f (PrimeSpectrum.comap a.toRingHom P)
    (constantPointsEquiv k f (PrimeSpectrum.comap a.toRingHom P))).mp rfl
  exact h

end

end OAI.AlgebraicGeometry.GroupSchemes.ConstantPoints.FiniteEtale
