import OAI.NumberTheory.ArithmeticGroups.Lattices.Archimedean.Quotient
import OAI.NumberTheory.Quaternion.Arithmetic.AdelicPolynomialInvariants

/-! # Minkowski Local Projections -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.MinkowskiLocalProjections

noncomputable section

section

/-! Polynomial invariants of local matrix groups are preserved by
their actual real representation on Minkowski coordinate space. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField _root_.NumberField.mixedEmbedding OAI.NumberTheory.ArithmeticGroups.Lattices.Archimedean.Quotient.Construction

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

def mixedPolynomialValue (p : MvPolynomial (Fin n) F) (x : Fin n → mixedSpace F) : mixedSpace F :=
  MvPolynomial.eval₂Hom (mixedEmbedding F) x p

omit [NumberField F] in
theorem continuous_mixedPolynomialValue (p : MvPolynomial (Fin n) F) :
    Continuous (mixedPolynomialValue p) := by
  change Continuous (fun x : Fin n → mixedSpace F => MvPolynomial.eval₂ (mixedEmbedding F) x p)
  convert MvPolynomial.continuous_eval (p.map (mixedEmbedding F)) using 1
  funext x
  simp only [MvPolynomial.eval_map]

omit [NumberField F] in
theorem mixedPolynomialValue_diagonal (p : MvPolynomial (Fin n) F) (x : Fin n → F) :
    mixedPolynomialValue p (fun i => mixedEmbedding F (x i)) = mixedEmbedding F (MvPolynomial.eval x p) :=
  (MvPolynomial.map_eval₂Hom (RingHom.id F) x (mixedEmbedding F) p).symm

def mixedCompletionProjection (v : InfinitePlace F) : mixedSpace F →+* v.Completion :=
  (Pi.evalRingHom (fun w : InfinitePlace F => w.Completion) v).comp
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toRingHom

omit [NumberField F] in
theorem mixedCompletionProjection_embedding (v : InfinitePlace F) :
    (mixedCompletionProjection v).comp (mixedEmbedding F) = algebraMap F v.Completion := by
  apply RingHom.ext
  intro x
  change ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (mixedEmbedding F x)) v =
    algebraMap F v.Completion x
  rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  exact congrFun ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm_apply_apply
    (algebraMap F (InfiniteAdeleRing F) x)) v

omit [NumberField F] in
theorem mixedCompletionProjection_archimedeanMatrix (g : ArithmeticGroups.Lattices.Archimedean.ExteriorAction.Construction.FullArchimedeanSL F n) (v : InfinitePlace F) :
    (mixedCompletionProjection v).mapMatrix (ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.archimedeanMixedSL F n g).val = (g v).val := by
  apply Matrix.ext
  intro i j
  change ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
    (InfiniteAdeleRing.ringEquiv_mixedSpace F (fun w => g w i j))) v = g v i j
  exact congrFun ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm_apply_apply (fun w => g w i j)) v

omit [NumberField F] in
theorem mixedPolynomialValue_archimedean_invariant (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (p : MvPolynomial (Fin n) F)
    (hp : ∀ (v : InfinitePlace F) (h : G.AtPlace v) (x : Fin n → v.Completion),
      MvPolynomial.eval₂Hom (algebraMap F v.Completion) (h.val.val *ᵥ x) p =
        MvPolynomial.eval₂Hom (algebraMap F v.Completion) x p)
    (g : G.ArchimedeanProduct Set.univ) (x : Fin n → mixedSpace F) :
    mixedPolynomialValue p (ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.archimedeanRealRepresentation F n (ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.fullArchimedeanPointsEquiv G g).val x) =
      mixedPolynomialValue p x := by
  apply (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.injective
  funext v
  let π := mixedCompletionProjection v
  let h := (ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.fullArchimedeanPointsEquiv G g).val
  have hvec : (fun i => π (ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.archimedeanRealRepresentation F n h x i)) =
      (h v).val *ᵥ (fun i => π (x i)) := by
    have hM : (ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.archimedeanMixedSL F n h).val.map π = (h v).val :=
      mixedCompletionProjection_archimedeanMatrix h v
    funext i
    have hi := RingHom.map_mulVec π (ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.archimedeanMixedSL F n h).val x i
    rw [hM] at hi
    exact hi
  change π (MvPolynomial.eval₂Hom (mixedEmbedding F)
    (ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.archimedeanRealRepresentation F n h x) p) = π (MvPolynomial.eval₂Hom (mixedEmbedding F) x p)
  rw [MvPolynomial.map_eval₂Hom, MvPolynomial.map_eval₂Hom, mixedCompletionProjection_embedding, hvec]
  exact hp v (g ⟨v, Set.mem_univ v⟩) (fun i => π (x i))

end

/-! Continuous projections from Minkowski coordinates to individual
archimedean completions, with compatibility with matrix actions. -/

open scoped Classical _root_.Matrix
open _root_.NumberField _root_.NumberField.mixedEmbedding OAI.NumberTheory.ArithmeticGroups.Lattices.Archimedean.Quotient.Construction

variable {F : Type} [Field F] {n : ℕ}

theorem mixedCompletionProjection_continuous (v : InfinitePlace F) :
    Continuous (mixedCompletionProjection v) := by
  by_cases hv : v.IsReal
  · apply (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff.mpr
    convert (continuous_apply (⟨v, hv⟩ : {w : InfinitePlace F // w.IsReal})).comp continuous_fst using 1
    funext x
    exact congrArg (fun y : mixedSpace F => y.1 ⟨v, hv⟩)
      ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply x)
  · have hv' : v.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hv
    apply (InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff.mpr
    convert (continuous_apply (⟨v, hv'⟩ : {w : InfinitePlace F // w.IsComplex})).comp continuous_snd using 1
    funext x
    exact congrArg (fun y : mixedSpace F => y.2 ⟨v, hv'⟩)
      ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply x)

theorem mixedCompletionProjection_archimedean_vector (g : ArithmeticGroups.Lattices.Archimedean.ExteriorAction.Construction.FullArchimedeanSL F n)
    (x : Fin n → mixedSpace F) (v : InfinitePlace F) :
    (fun i => mixedCompletionProjection v (ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.archimedeanRealRepresentation F n g x i)) =
      (g v).val *ᵥ (fun i => mixedCompletionProjection v (x i)) := by
  have hM : (ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.archimedeanMixedSL F n g).val.map (mixedCompletionProjection v) = (g v).val :=
    mixedCompletionProjection_archimedeanMatrix g v
  funext i
  have hi := RingHom.map_mulVec (mixedCompletionProjection v) (ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.archimedeanMixedSL F n g).val x i
  rw [hM] at hi
  exact hi

end

end OAI.NumberTheory.Quaternion.Arithmetic.MinkowskiLocalProjections
