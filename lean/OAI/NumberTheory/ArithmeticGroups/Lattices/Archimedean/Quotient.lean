import OAI.NumberTheory.ArithmeticGroups.Lattices.Archimedean.ClosedImage
import OAI.NumberTheory.ArithmeticGroups.Lattices.Archimedean.IntegralDiscrete

/-! # Quotient -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Archimedean.Quotient.Construction

noncomputable section

section

/-! The full archimedean arithmetic quotient embeds as a closed subspace
of the ambient special-linear arithmetic quotient. -/

open scoped Classical _root_.NumberField

theorem fullArchimedeanMatrixGroup_quotient_closedEmbedding
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hconn : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple) :
    Topology.IsClosedEmbedding
      (ClosedOrbitQuotient.Construction.subgroupCosetMap (ExteriorAction.Construction.fullArchimedeanMatrixGroup G) (ExteriorAction.Construction.fullArchimedeanIntegralSL k n)) := by
  let : DiscreteTopology (ExteriorAction.Construction.fullArchimedeanIntegralSL k n) := IntegralDiscrete.Construction.fullArchimedeanIntegralSL_discrete k n
  let : SigmaCompactSpace (ExteriorAction.Construction.fullArchimedeanMatrixGroup G) :=
    (IntegralDiscrete.Construction.fullArchimedeanMatrixGroup_closed G).sigmaCompactSpace
  exact StabilizerSaturation.Construction.subgroup_quotient_embedding_of_closed_image _ _
    (ClosedImage.Construction.fullArchimedeanMatrixGroup_quotient_image_closed G hconn hsemi)

end

section

/-! Comparison of the full archimedean subgroup with the point-product
and integral stabilizer used by the stable Lattices statement. -/

open scoped Classical _root_.NumberField
open _root_.NumberField

theorem matrixGroup_mem_iff_scalar_extension
    {k K : Type} [Field k] [Field K] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (ι : k →+* K) (g : Algebraic.SL n k) :
    Matrix.SpecialLinearGroup.map ι g ∈ G.subgroup K ι ↔ g ∈ G.subgroup k (RingHom.id k) := by
  constructor
  · intro hg
    apply (G.mem_iff k (RingHom.id k) g).mpr
    intro p hp
    apply ι.injective
    have he := (G.mem_iff K ι _).mp hg p hp
    simpa only [Algebraic.evaluateMatrix, MvPolynomial.map_eval₂Hom, map_zero,
      Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply, RingHom.comp_id] using he
  · intro hg
    exact (G.map (RingHom.id k) ι ⟨g, hg⟩).property

theorem fullArchimedeanSLMap_mem_iff
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (g : Algebraic.SL n k) :
    ExteriorAction.Construction.fullArchimedeanSLMap k n g ∈ ExteriorAction.Construction.fullArchimedeanMatrixGroup G ↔
      g ∈ G.subgroup k (RingHom.id k) := by
  constructor
  · intro hg
    let v : InfinitePlace k := Classical.choice inferInstance
    exact (matrixGroup_mem_iff_scalar_extension G (algebraMap k v.Completion) g).mp (hg v)
  · intro hg v
    exact (matrixGroup_mem_iff_scalar_extension G (algebraMap k v.Completion) g).mpr hg

def fullArchimedeanRationalPointMap
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    G.RationalPoints →* ExteriorAction.Construction.fullArchimedeanMatrixGroup G where
  toFun g := ⟨ExteriorAction.Construction.fullArchimedeanSLMap k n g.val, (fullArchimedeanSLMap_mem_iff G g.val).mpr g.property⟩
  map_one' := Subtype.ext (map_one (ExteriorAction.Construction.fullArchimedeanSLMap k n))
  map_mul' g h := Subtype.ext (map_mul (ExteriorAction.Construction.fullArchimedeanSLMap k n) g.val h.val)

def fullArchimedeanPointsEquiv
    {k : Type} [Field k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    G.ArchimedeanProduct Set.univ ≃ₜ* ExteriorAction.Construction.fullArchimedeanMatrixGroup G where
  toFun g := ⟨fun v => (g ⟨v, Set.mem_univ v⟩).val, fun v => (g ⟨v, Set.mem_univ v⟩).property⟩
  invFun g v := ⟨g.val v.val, g.property v.val⟩
  left_inv g := by funext v; rfl
  right_inv g := by apply Subtype.ext; rfl
  map_mul' g h := by apply Subtype.ext; rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro v
    exact continuous_subtype_val.comp
      (continuous_apply (⟨v, Set.mem_univ v⟩ : (Set.univ : Set (InfinitePlace k))))
  continuous_invFun := by
    apply continuous_pi
    intro v
    exact ((continuous_apply v.val).comp continuous_subtype_val).subtype_mk _

theorem fullArchimedeanPointsEquiv_diagonal
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (g : G.RationalPoints) :
    fullArchimedeanPointsEquiv G (G.diagonal Set.univ g) = fullArchimedeanRationalPointMap G g := rfl

theorem fullArchimedean_standard_arithmetic_subgroup
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    (G.latticeStabilizer (IntegralLattice.FullLattice.standard k n)).map (fullArchimedeanRationalPointMap G) =
      (ExteriorAction.Construction.fullArchimedeanIntegralSL k n).subgroupOf (ExteriorAction.Construction.fullArchimedeanMatrixGroup G) := by
  ext g
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨A, hA⟩ := (Integral.Matrices.Construction.standard_lattice_stabilizer_iff_integral G q).mp hq
    exact ⟨A, congrArg (ExteriorAction.Construction.fullArchimedeanSLMap k n) hA⟩
  · rintro ⟨A, hA⟩
    let q := Matrix.SpecialLinearGroup.map (algebraMap (𝓞 k) k) A
    have hq : q ∈ G.subgroup k (RingHom.id k) := by
      apply (fullArchimedeanSLMap_mem_iff G q).mp
      change ExteriorAction.Construction.fullArchimedeanSLMap k n q = g.val at hA
      exact hA.symm ▸ g.property
    refine ⟨⟨q, hq⟩, (Integral.Matrices.Construction.standard_lattice_stabilizer_iff_integral G ⟨q, hq⟩).mpr ⟨A, rfl⟩, ?_⟩
    exact Subtype.ext hA

end

section

/-! The archimedean matrix product is a special-linear group over the
mixed real/complex algebra. This is the matrix realization used for
restriction of scalars to the reals. -/

open scoped Classical
open _root_.NumberField _root_.NumberField.mixedEmbedding

def archimedeanAdeleMatrix {k : Type} [Field k] {n : ℕ} (g : ExteriorAction.Construction.FullArchimedeanSL k n) :
    Matrix (Fin n) (Fin n) (InfiniteAdeleRing k) := Matrix.of (fun i j v => g v i j)

theorem archimedeanAdeleMatrix_det {k : Type} [Field k] {n : ℕ} (g : ExteriorAction.Construction.FullArchimedeanSL k n) :
    (archimedeanAdeleMatrix g).det = 1 := by
  funext v
  let ev : InfiniteAdeleRing k →+* v.Completion := Pi.evalRingHom (fun w => w.Completion) v
  have he : (archimedeanAdeleMatrix g).map ev = (g v : Matrix (Fin n) (Fin n) v.Completion) := rfl
  change ev (archimedeanAdeleMatrix g).det = 1
  rw [RingHom.map_det, RingHom.mapMatrix_apply, he, Matrix.SpecialLinearGroup.det_coe]

def archimedeanAdeleSL (k : Type) [Field k] (n : ℕ) :
    ExteriorAction.Construction.FullArchimedeanSL k n →* Algebraic.SL n (InfiniteAdeleRing k) where
  toFun g := ⟨archimedeanAdeleMatrix g, archimedeanAdeleMatrix_det g⟩
  map_one' := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    funext v
    change (1 : Matrix (Fin n) (Fin n) v.Completion) i j =
      (1 : Matrix (Fin n) (Fin n) (InfiniteAdeleRing k)) i j v
    simp only [Matrix.one_apply]
    split_ifs <;> rfl
  map_mul' g h := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    funext v
    let ev : InfiniteAdeleRing k →+* v.Completion := Pi.evalRingHom (fun w => w.Completion) v
    change (∑ l, g v i l * h v l j) =
      ev (∑ l, archimedeanAdeleMatrix g i l * archimedeanAdeleMatrix h l j)
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro l _
    rw [map_mul]
    rfl

def archimedeanMixedSL (k : Type) [Field k] (n : ℕ) :
    ExteriorAction.Construction.FullArchimedeanSL k n →* Algebraic.SL n (mixedSpace k) :=
  (Matrix.SpecialLinearGroup.map (InfiniteAdeleRing.ringEquiv_mixedSpace k).toRingHom).comp
    (archimedeanAdeleSL k n)

theorem archimedeanMixedSL_entry {k : Type} [Field k] {n : ℕ}
    (g : ExteriorAction.Construction.FullArchimedeanSL k n) (i j : Fin n) :
    archimedeanMixedSL k n g i j = InfiniteAdeleRing.ringEquiv_mixedSpace k (fun v => g v i j) := rfl

theorem archimedeanMixedSL_injective (k : Type) [Field k] (n : ℕ) :
    Function.Injective (archimedeanMixedSL k n) := by
  intro g h he
  funext v
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have hij := congrArg (fun z : Algebraic.SL n (mixedSpace k) => z i j) he
  exact congrFun ((InfiniteAdeleRing.ringEquiv_mixedSpace k).injective hij) v

theorem continuous_archimedeanMixedSL (k : Type) [Field k] (n : ℕ) :
    Continuous (archimedeanMixedSL k n) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun g : ExteriorAction.Construction.FullArchimedeanSL k n =>
    InfiniteAdeleRing.ringEquiv_mixedSpace k (fun v => g v i j))
  apply Discrete.Construction.continuous_adele_to_mixed.comp
  apply continuous_pi
  intro v
  exact (continuous_apply j).comp (Matrix.SpecialLinearGroup.continuous_apply _ (continuous_apply v) i)

theorem archimedeanMixedSL_surjective (k : Type) [Field k] (n : ℕ) :
    Function.Surjective (archimedeanMixedSL k n) := by
  intro A
  let B := Matrix.SpecialLinearGroup.map (InfiniteAdeleRing.ringEquiv_mixedSpace k).symm.toRingHom A
  let g : ExteriorAction.Construction.FullArchimedeanSL k n := fun v =>
    Matrix.SpecialLinearGroup.map
      (show InfiniteAdeleRing k →+* v.Completion from Pi.evalRingHom (fun w => w.Completion) v) B
  refine ⟨g, ?_⟩
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change InfiniteAdeleRing.ringEquiv_mixedSpace k
    ((InfiniteAdeleRing.ringEquiv_mixedSpace k).symm (A i j)) = A i j
  exact (InfiniteAdeleRing.ringEquiv_mixedSpace k).apply_symm_apply (A i j)

end

/-! Restriction of scalars gives a faithful, determinant-one real
representation on the Minkowski coordinate space. -/

open scoped Classical
open _root_.NumberField _root_.NumberField.mixedEmbedding

def archimedeanRealRepresentation (k : Type) [Field k] (n : ℕ) :
    ExteriorAction.Construction.FullArchimedeanSL k n →* ((Fin n → mixedSpace k) ≃ₗ[ℝ] (Fin n → mixedSpace k)) where
  toFun g := (Matrix.SpecialLinearGroup.toLin' (archimedeanMixedSL k n g)).restrictScalars ℝ
  map_one' := by
    apply LinearEquiv.ext
    intro x
    change Matrix.SpecialLinearGroup.toLin' (archimedeanMixedSL k n 1) x = x
    rw [map_one, map_one]
    rfl
  map_mul' g h := by
    apply LinearEquiv.ext
    intro x
    change Matrix.SpecialLinearGroup.toLin' (archimedeanMixedSL k n (g * h)) x =
      Matrix.SpecialLinearGroup.toLin' (archimedeanMixedSL k n g)
        (Matrix.SpecialLinearGroup.toLin' (archimedeanMixedSL k n h) x)
    rw [map_mul, map_mul]
    rfl

theorem archimedeanRealRepresentation_det (k : Type) [Field k] (n : ℕ)
    (g : ExteriorAction.Construction.FullArchimedeanSL k n) :
    (archimedeanRealRepresentation k n g).toLinearMap.det = 1 := by
  change ((Matrix.toLin' (archimedeanMixedSL k n g : Matrix (Fin n) (Fin n) (mixedSpace k))).restrictScalars ℝ).det = 1
  rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Matrix.SpecialLinearGroup.det_coe, map_one]

theorem archimedeanRealRepresentation_injective (k : Type) [Field k] (n : ℕ) :
    Function.Injective (archimedeanRealRepresentation k n) := by
  intro g h he
  apply archimedeanMixedSL_injective k n
  apply Matrix.SpecialLinearGroup.toLin'_injective
  apply LinearEquiv.ext
  intro x
  exact congrArg (fun f : (Fin n → mixedSpace k) ≃ₗ[ℝ] (Fin n → mixedSpace k) => f x) he

theorem continuous_archimedeanRealRepresentation_apply (k : Type) [Field k] (n : ℕ) :
    Continuous (fun a : ExteriorAction.Construction.FullArchimedeanSL k n × (Fin n → mixedSpace k) =>
      archimedeanRealRepresentation k n a.1 a.2) := by
  apply continuous_pi
  intro i
  change Continuous (fun a : ExteriorAction.Construction.FullArchimedeanSL k n × (Fin n → mixedSpace k) =>
    ∑ j, archimedeanMixedSL k n a.1 i j * a.2 j)
  apply continuous_finsetSum
  intro j _
  have hm : Continuous (fun a : ExteriorAction.Construction.FullArchimedeanSL k n × (Fin n → mixedSpace k) =>
      archimedeanMixedSL k n a.1 i j) :=
    (continuous_apply j).comp (Matrix.SpecialLinearGroup.continuous_apply _
      ((continuous_archimedeanMixedSL k n).comp continuous_fst) i)
  exact hm.mul ((continuous_apply j).comp continuous_snd)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Archimedean.Quotient.Construction
