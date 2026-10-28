import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.PresheafReindex
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.PresheafFunctorCongruence
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.OpenReindex
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.Fraction
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Products

/-! # Intrinsic -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.Intrinsic.IntrinsicComparison

noncomputable section

/-! The selected geometric source diagram and the native principal
diagram on that source open have the same original global comparison. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {Y Z : Scheme.{u}} (π : Y ⟶ Z)
  (U : Z.Opens) (hU : IsAffineOpen U)
  (V : Y.Opens) (hV : IsAffineOpen V) (hVU : V ≤ π ⁻¹ᵁ U)
  {m : ℕ} (t : Fin m → Γ(Z,U))

abbrev geometric := OpenReindex.geometricOpens π U hU V
abbrev native := Principal.AdditiveSections.opens V hV
abbrev reindex := OpenReindex.reindex π U V hVU
abbrev family := PrincipalPoint.Fraction.family U t

local instance native_tuples : ∀ (d : ℕ) (a : Fin (d+1) → ULift (Fin m)),
    PreservesLimit (Discrete.functor (((reindex π U V hVU).obj ∘ family U t) ∘ a)) (native V hV) :=
  fun _ a => AffinePrincipal.Products.preserves Y V hV (((reindex π U V hVU).obj ∘ family U t) ∘ a)

local instance intermediate_tuples : ∀ (d : ℕ) (a : Fin (d+1) → ULift (Fin m)),
    PreservesLimit (Discrete.functor (family U t ∘ a)) (reindex π U V hVU ⋙ native V hV) :=
  fun d a => AugmentedCech.AmbientReindex.composite_tuple
    (reindex π U V hVU) (native V hV) (family U t) d a

include hV hVU in
theorem geometric_tuples : ∀ (d : ℕ) (a : Fin (d+1) → ULift (Fin m)),
    PreservesLimit (Discrete.functor (family U t ∘ a)) (geometric π U hU V) :=
  Principal.PresheafFunctorCongruence.tuple_preserves
    (reindex π U V hVU ⋙ native V hV)
    (OpenReindex.opens_eq π U hU V hV hVU) (family U t)

variable {A : Type v} [Category A] [Abelian A] [HasProducts.{u} A] [HasCoproducts.{0} A]
  (K : CochainComplex (Y.Opensᵒᵖ ⥤ A) ℕ)

def sourceIso :=
  Principal.PresheafFunctorCongruence.sourceIso (geometric π U hU V)
    (OpenReindex.opens_eq π U hU V hV hVU).symm (family U t) K ≪≫
  Principal.PresheafReindex.sourceIso (reindex π U V hVU) (native V hV) (family U t) K

variable {κ ν μ ρ : Type u}
  [LinearOrder κ] [LinearOrder ν] [LinearOrder μ] [LinearOrder ρ]
  (B : κ → Y.Opens) (J : ν → Y.Opens)
  (r : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk (ULift (Fin m))
    ((geometric π U hU V).obj ∘ family U t))
  (s : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk κ B)
  (W : μ → Y.Opens) (T : ρ → Y.Opens)
  (l : FormalCoproduct.mk ρ T ⟶ FormalCoproduct.mk (WithBot κ)
    (RelativeCech.Intersections.cover
      ((geometric π U hU V).obj (⊤_ (Principal.SectionPresheaf.Index U))) B))
  (j : FormalCoproduct.mk ρ T ⟶ FormalCoproduct.mk μ W)
  (q : ℕ)
  [hrel : IsIso (RelativeCech.Refinement.homology
    ((geometric π U hU V).obj (⊤_ (Principal.SectionPresheaf.Index U))) B J s K q)]
  [IsIso (homologyMap (OrderedCech.Refinement.totalMap W T j K) q)]

abbrev localRefinement := Principal.PresheafFunctorCongruence.localRefinement
  (geometric π U hU V) (OpenReindex.opens_eq π U hU V hV hVU).symm
  (family U t) J r

abbrev intermediateRefinement := Principal.PresheafFunctorCongruence.globalRefinement
  (geometric π U hU V) (OpenReindex.opens_eq π U hU V hV hVU).symm B T l

abbrev globalRefinement := Principal.PresheafReindex.targetRefinement
  (reindex π U V hVU) (native V hV) B T (intermediateRefinement π U hU V hV hVU B T l)

include hrel in
theorem intermediate_isIso : IsIso (RelativeCech.Refinement.homology
    ((reindex π U V hVU ⋙ native V hV).obj (⊤_ (Principal.SectionPresheaf.Index U))) B J s K q) :=
  Principal.PresheafFunctorCongruence.relative_isIso (geometric π U hU V)
    (OpenReindex.opens_eq π U hU V hV hVU).symm B J s K q

include hrel hVU in
theorem native_isIso : IsIso (RelativeCech.Refinement.homology
    ((native V hV).obj (⊤_ (Principal.SectionPresheaf.Index V))) B J s K q) := by
  let := intermediate_isIso π U hU V hV hVU K B J s q
  exact Principal.Tail.Comparison.relative_isIso
    ((reindex π U V hVU ⋙ native V hV).obj (⊤_ (Principal.SectionPresheaf.Index U)))
    B J s K q ((native V hV).obj (⊤_ (Principal.SectionPresheaf.Index V)))
    (AugmentedCech.AmbientReindex.terminal_eq (reindex π U V hVU) (native V hV))

theorem comparison :
    letI := geometric_tuples π U hU V hV hVU t
    letI := native_isIso π U hU V hV hVU K B J s q
    homologyMap (sourceIso π U hU V hV hVU t K).hom q ≫
      Principal.PresheafCover.Comparison.comparison (native V hV)
        ((reindex π U V hVU).obj ∘ family U t) B J
        (localRefinement π U hU V hV hVU t J r) s W T
        (globalRefinement π U hU V hV hVU B T l) j K q =
    Principal.PresheafCover.Comparison.comparison (geometric π U hU V) (family U t)
      B J r s W T l j K q := by
  let := geometric_tuples π U hU V hV hVU t
  let := intermediate_isIso π U hU V hV hVU K B J s q
  let := native_isIso π U hU V hV hVU K B J s q
  have h₁ := Principal.PresheafFunctorCongruence.comparison (geometric π U hU V)
    (OpenReindex.opens_eq π U hU V hV hVU).symm
    (family U t) B J r s W T l j K q
  let : IsIso (RelativeCech.Refinement.homology
      ((native V hV).obj ((reindex π U V hVU).obj
        (⊤_ (Principal.SectionPresheaf.Index U)))) B J s K q) :=
    intermediate_isIso π U hU V hV hVU K B J s q
  have h₂ := Principal.PresheafReindex.comparison (reindex π U V hVU) (native V hV)
    (family U t) B J (localRefinement π U hU V hV hVU t J r) s W T
    (intermediateRefinement π U hU V hV hVU B T l) j K q
  simp only [sourceIso, Iso.trans_hom, homologyMap_comp, Category.assoc]
  rw [h₂]
  exact h₁

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.Intrinsic.IntrinsicComparison
