import OAI.NumberTheory.Quaternion.Arithmetic.FiniteSpecialLinearCorrection
import OAI.NumberTheory.ArithmeticGroups.Lattices.QuotientMeasure
import OAI.NumberTheory.Quaternion.Arithmetic.Ambient

/-! # Adelic Group -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.AdelicGroup

noncomputable section

section

/-! The product of all archimedean points and the finite restricted
product, with its actual rational diagonal. -/

open scoped Classical
open OAI.NumberTheory.ArithmeticGroups.Lattices.QuotientMeasure.Construction Set

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

abbrev FullAdelicGroupPoints (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) :=
  G.ArchimedeanProduct Set.univ × FiniteAdelicMatrices.FiniteAdelicGroupPoints G

def diagonalFullAdelic (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) : G.RationalPoints →* FullAdelicGroupPoints G :=
  (G.diagonal Set.univ).prod (FiniteAdelicComparison.diagonalFiniteAdelic G)

theorem fullAdelic_quotient_compact_of_corrections (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (K : Set (FullAdelicGroupPoints G)) (hK : IsCompact K)
    (hc : ∀ g : FullAdelicGroupPoints G, ∃ q : G.RationalPoints, g * diagonalFullAdelic G q ∈ K) :
    CompactSpace (FullAdelicGroupPoints G ⧸ (diagonalFullAdelic G).range) := by
  apply ArithmeticGroups.Lattices.QuotientMeasure.Construction.compact_quotient_of_compact_cover (diagonalFullAdelic G).range K hK
  intro g
  obtain ⟨q, hq⟩ := hc g
  refine ⟨g * diagonalFullAdelic G q, hq, diagonalFullAdelic G q⁻¹, ⟨q⁻¹, rfl⟩, ?_⟩
  rw [map_inv, mul_inv_cancel_right]

end

/-! Open adelic subgroups integral outside a finite set of places,
and their surjective projections to the selected local product. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain Set Filter

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

def fullAdelicEvaluation (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (v : LocalAdeles.Place F) :
    FullAdelicGroupPoints G →* LocalAdeles.LocalPoints G v where
  toFun g := match v with
    | .inl w => g.1 ⟨w, mem_univ w⟩
    | .inr w => g.2 w
  map_one' := by cases v <;> rfl
  map_mul' g h := by cases v <;> rfl

theorem fullAdelicEvaluation_continuous (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (v : LocalAdeles.Place F) :
    Continuous (fullAdelicEvaluation G v) := by
  cases v with
  | inl w => exact (continuous_apply (⟨w, mem_univ w⟩ : (Set.univ : Set (NumberField.InfinitePlace F)))).comp continuous_fst
  | inr w => exact (RestrictedProduct.continuous_eval w).comp continuous_snd

theorem fullAdelicEvaluation_diagonal (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (v : LocalAdeles.Place F) (q : G.RationalPoints) :
    fullAdelicEvaluation G v (diagonalFullAdelic G q) = LocalAdeles.diagonalLocal G v q := by
  cases v <;> rfl

def fullAdelicIntegralOutside (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (S : Finset (LocalAdeles.Place F)) :
    Subgroup (FullAdelicGroupPoints G) where
  carrier := {g | ∀ v : HeightOneSpectrum (𝓞 F), Sum.inr v ∉ S → g.2 v ∈ LocalAdeles.integralLocalSubgroup G (.inr v)}
  one_mem' v _ := (LocalAdeles.integralLocalSubgroup G (.inr v)).one_mem
  mul_mem' hg hh v hv := (LocalAdeles.integralLocalSubgroup G (.inr v)).mul_mem (hg v hv) (hh v hv)
  inv_mem' hg v hv := (LocalAdeles.integralLocalSubgroup G (.inr v)).inv_mem (hg v hv)

theorem fullAdelicIntegralOutside_isOpen (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (S : Finset (LocalAdeles.Place F)) :
    IsOpen (fullAdelicIntegralOutside G S : Set (FullAdelicGroupPoints G)) :=
  (RestrictedProduct.isOpen_forall_imp_mem
    (fun v : HeightOneSpectrum (𝓞 F) => LocalAdeles.integralLocalSubgroup_isOpen G (.inr v))).preimage continuous_snd

def fullAdelicProjection (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (S : Finset (LocalAdeles.Place F)) :
    FullAdelicGroupPoints G →* Ambient.OmittedLocalProduct G S :=
  MonoidHom.pi (fun v => fullAdelicEvaluation G v.val)

theorem fullAdelicProjection_continuous (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (S : Finset (LocalAdeles.Place F)) :
    Continuous (fullAdelicProjection G S) :=
  continuous_pi (fun v => fullAdelicEvaluation_continuous G v.val)

def selectedLocalExtension (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (S : Finset (LocalAdeles.Place F))
    (x : Ambient.OmittedLocalProduct G S) (v : LocalAdeles.Place F) : LocalAdeles.LocalPoints G v :=
  if hv : v ∈ S then x ⟨v, hv⟩ else 1

theorem selectedLocalExtension_of_mem (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (S : Finset (LocalAdeles.Place F))
    (x : Ambient.OmittedLocalProduct G S) (v : LocalAdeles.Place F) (hv : v ∈ S) :
    selectedLocalExtension G S x v = x ⟨v, hv⟩ := dite_eq_left hv

theorem selectedLocalExtension_of_not_mem (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (S : Finset (LocalAdeles.Place F))
    (x : Ambient.OmittedLocalProduct G S) (v : LocalAdeles.Place F) (hv : v ∉ S) :
    selectedLocalExtension G S x v = 1 := dite_eq_right hv

def finiteAdelicExtension (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (S : Finset (LocalAdeles.Place F))
    (x : Ambient.OmittedLocalProduct G S) : FiniteAdelicMatrices.FiniteAdelicGroupPoints G :=
   ⟨fun v : HeightOneSpectrum (𝓞 F) => selectedLocalExtension G S x (.inr v), by
     have hfin : {v : HeightOneSpectrum (𝓞 F) | Sum.inr v ∈ S}.Finite :=
       S.finite_toSet.preimage Sum.inr_injective.injOn
     filter_upwards [hfin.compl_mem_cofinite] with v hv
     rw [selectedLocalExtension_of_not_mem G S x (.inr v) hv]
     exact (LocalAdeles.integralLocalSubgroup G (.inr v)).one_mem⟩

def fullAdelicExtension (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (S : Finset (LocalAdeles.Place F))
    (x : Ambient.OmittedLocalProduct G S) : FullAdelicGroupPoints G :=
  (fun w => selectedLocalExtension G S x (.inl w.val),
    finiteAdelicExtension G S x)

theorem fullAdelicExtension_integralOutside (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (S : Finset (LocalAdeles.Place F))
    (x : Ambient.OmittedLocalProduct G S) : fullAdelicExtension G S x ∈ fullAdelicIntegralOutside G S := by
  intro v hv
  change selectedLocalExtension G S x (.inr v) ∈ LocalAdeles.integralLocalSubgroup G (.inr v)
  rw [selectedLocalExtension_of_not_mem G S x (.inr v) hv]
  exact (LocalAdeles.integralLocalSubgroup G (.inr v)).one_mem

theorem fullAdelicProjection_extension (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (S : Finset (LocalAdeles.Place F))
    (x : Ambient.OmittedLocalProduct G S) : fullAdelicProjection G S (fullAdelicExtension G S x) = x := by
  funext v
  rcases v with ⟨v, hv⟩
  cases v with
  | inl w => exact selectedLocalExtension_of_mem G S x (.inl w) hv
  | inr w => exact selectedLocalExtension_of_mem G S x (.inr w) hv

def integralOutsideProjection (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (S : Finset (LocalAdeles.Place F)) :
    fullAdelicIntegralOutside G S →* Ambient.OmittedLocalProduct G S :=
  (fullAdelicProjection G S).comp (fullAdelicIntegralOutside G S).subtype

theorem integralOutsideProjection_continuous (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (S : Finset (LocalAdeles.Place F)) :
    Continuous (integralOutsideProjection G S) :=
  (fullAdelicProjection_continuous G S).comp continuous_subtype_val

theorem integralOutsideProjection_surjective (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (S : Finset (LocalAdeles.Place F)) :
    Function.Surjective (integralOutsideProjection G S) := fun x =>
  ⟨⟨fullAdelicExtension G S x, fullAdelicExtension_integralOutside G S x⟩, fullAdelicProjection_extension G S x⟩

theorem diagonalFullAdelic_mem_integralOutside (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (S : Finset (LocalAdeles.Place F)) (q : G.RationalPoints) :
    diagonalFullAdelic G q ∈ fullAdelicIntegralOutside G S ↔ q ∈ Groups.sIntegralPoints G (S : Set (LocalAdeles.Place F)) := by
  constructor
  · intro h v hv
    cases v with
    | inl w => exact ⟨fun _ _ => Subring.mem_top _, fun _ _ => Subring.mem_top _⟩
    | inr w => exact h w hv
  · intro h v hv
    exact h (.inr v) hv

end

end OAI.NumberTheory.Quaternion.Arithmetic.AdelicGroup
