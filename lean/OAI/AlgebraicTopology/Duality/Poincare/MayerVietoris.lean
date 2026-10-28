import OAI.AlgebraicTopology.Duality.Poincare.Property
import OAI.AlgebraicTopology.Duality.Poincare.SignedFiveLemma
import OAI.AlgebraicTopology.Duality.Poincare.CompactSupportMayerVietoris
import OAI.AlgebraicTopology.Duality.Poincare.OpenRational
import OAI.AlgebraicTopology.Duality.Poincare.NestedOpenCapNaturality
import OAI.AlgebraicTopology.Duality.Poincare.CanonicalCapMayerVietoris

/-! # Mayer Vietoris -/

namespace OAI.AlgebraicTopology.Duality.Poincare

noncomputable section

/-!
# Mayer--Vietoris induction for canonical cap duality

The cohomological sequence has signs (+,+), (+,-), while the homological
sequence has signs (+,-), (+,+). Consequently the middle vertical map is
the direct sum of the first canonical cap and the negative of the second.
All maps here are the previously constructed canonical cap maps and the
actual open-subspace Mayer--Vietoris maps.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open scoped _root_.Manifold

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]

/-- The signed direct sum of the actual canonical cap maps. -/
def MayerVietoris.poincareMayerVietorisMiddle (U V : Opens M) (p q : ℕ) (hpq : p + q = 2 * d) :
    CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) p ⊞
        CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of V) p ⟶
      OpenRational.openRationalHomology (X := TopCat.of M) U q ⊞
        OpenRational.openRationalHomology (X := TopCat.of M) V q :=
  biprod.map (ComplexManifoldCap.complexManifoldCompactSupportCap d (M := U) p q hpq)
    (-ComplexManifoldCap.complexManifoldCompactSupportCap d (M := V) p q hpq)

/-- The intersection-inclusion square commutes with the required signs. -/
@[reassoc]
theorem MayerVietoris.poincareMayerVietoris_first (U V : Opens M) (p q : ℕ)
    (hpq : p + q = 2 * d) :
    CompactSupportMayerVietoris.compactSupportMayerVietorisFirst (X := TopCat.of M) U V p ≫
        MayerVietoris.poincareMayerVietorisMiddle d U V p q hpq =
      ComplexManifoldCap.complexManifoldCompactSupportCap d (M := ↥(U ⊓ V)) p q hpq ≫
        OpenRational.openRationalMayerVietorisFirst (X := TopCat.of M) U V q := by
  apply biprod.hom_ext
  · simpa [CompactSupportMayerVietoris.compactSupportMayerVietorisFirst, MayerVietoris.poincareMayerVietorisMiddle,
      OpenRational.openRationalMayerVietorisFirst] using
      NestedOpenCapNaturality.complexManifoldCompactSupportCap_opensInclusion d (U ⊓ V) U inf_le_left p q hpq
  · simpa [CompactSupportMayerVietoris.compactSupportMayerVietorisFirst, MayerVietoris.poincareMayerVietorisMiddle,
      OpenRational.openRationalMayerVietorisFirst] using
      congrArg Neg.neg
        (NestedOpenCapNaturality.complexManifoldCompactSupportCap_opensInclusion d (U ⊓ V) V inf_le_right p q hpq)

/-- The union-inclusion square commutes with the required signs. -/
@[reassoc]
theorem MayerVietoris.poincareMayerVietoris_second (U V : Opens M) (p q : ℕ)
    (hpq : p + q = 2 * d) :
    CompactSupportMayerVietoris.compactSupportMayerVietorisSecond (X := TopCat.of M) U V p ≫
        ComplexManifoldCap.complexManifoldCompactSupportCap d (M := ↥(U ⊔ V)) p q hpq =
      MayerVietoris.poincareMayerVietorisMiddle d U V p q hpq ≫
        OpenRational.openRationalMayerVietorisSecond (X := TopCat.of M) U V q := by
  apply biprod.hom_ext'
  · simpa [CompactSupportMayerVietoris.compactSupportMayerVietorisSecond, MayerVietoris.poincareMayerVietorisMiddle,
      OpenRational.openRationalMayerVietorisSecond] using
      NestedOpenCapNaturality.complexManifoldCompactSupportCap_opensInclusion d U (U ⊔ V) le_sup_left p q hpq
  · simpa [CompactSupportMayerVietoris.compactSupportMayerVietorisSecond, MayerVietoris.poincareMayerVietorisMiddle,
      OpenRational.openRationalMayerVietorisSecond] using
      congrArg Neg.neg
        (NestedOpenCapNaturality.complexManifoldCompactSupportCap_opensInclusion d V (U ⊔ V) le_sup_right p q hpq)

/-- Complementary-degree isomorphisms on the two opens give the signed
middle isomorphism in the actual Mayer--Vietoris diagram. -/
theorem MayerVietoris.poincareMayerVietorisMiddle_isIso (U V : Opens M)
    (hU : Property.HasCanonicalPoincareDuality d U) (hV : Property.HasCanonicalPoincareDuality d V)
    (p q : ℕ) (hpq : p + q = 2 * d) :
    IsIso (MayerVietoris.poincareMayerVietorisMiddle d U V p q hpq) := by
  let : IsIso (ComplexManifoldCap.complexManifoldCompactSupportCap d (M := U) p q hpq) :=
    hU.cap_isIso p q hpq
  let : IsIso (ComplexManifoldCap.complexManifoldCompactSupportCap d (M := V) p q hpq) :=
    hV.cap_isIso p q hpq
  exact (biprod.mapIso
    (asIso (ComplexManifoldCap.complexManifoldCompactSupportCap d (M := U) p q hpq))
    (-asIso (ComplexManifoldCap.complexManifoldCompactSupportCap d (M := V) p q hpq))).isIso_hom

/-- The higher-degree vanishing part of the induction is preserved under
binary open unions by the actual compact-support exact sequence. -/
theorem Property.HasCanonicalPoincareDuality.cohomology_isZero_sup (U V : Opens M)
    (hU : Property.HasCanonicalPoincareDuality d U) (hV : Property.HasCanonicalPoincareDuality d V)
    (hUV : Property.HasCanonicalPoincareDuality d ↥(U ⊓ V)) (p : ℕ) (hp : 2 * d < p) :
    IsZero (CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of ↥(U ⊔ V)) p) := by
  exact ((CompactSupportMayerVietoris.compactSupportMayerVietorisSequence_exact (X := TopCat.of M) U V p).exact 1).isZero_of_both_isZero
      ((biprod_isZero_iff _ _).mpr ⟨hU.cohomology_isZero p hp, hV.cohomology_isZero p hp⟩)
      (hUV.cohomology_isZero (p + 1) (by omega))

/-- The top cohomological degree, including real dimension zero, uses the
true degree-zero homology endpoint and the proved higher vanishing. -/
theorem Property.HasCanonicalPoincareDuality.cap_sup_isIso_zero (U V : Opens M)
    (hU : Property.HasCanonicalPoincareDuality d U) (hV : Property.HasCanonicalPoincareDuality d V)
    (hUV : Property.HasCanonicalPoincareDuality d ↥(U ⊓ V))
    (p : ℕ) (hp : p + 0 = 2 * d) :
    IsIso (ComplexManifoldCap.complexManifoldCompactSupportCap d (M := ↥(U ⊔ V)) p 0 hp) := by
  let : IsIso (ComplexManifoldCap.complexManifoldCompactSupportCap d (M := ↥(U ⊓ V)) p 0 hp) :=
    hUV.cap_isIso p 0 hp
  let : IsIso (MayerVietoris.poincareMayerVietorisMiddle d U V p 0 hp) :=
    MayerVietoris.poincareMayerVietorisMiddle_isIso d U V hU hV p 0 hp
  let φ :
      ComposableArrows.mk₂ (CompactSupportMayerVietoris.compactSupportMayerVietorisFirst (X := TopCat.of M) U V p)
        (CompactSupportMayerVietoris.compactSupportMayerVietorisSecond (X := TopCat.of M) U V p) ⟶
      ComposableArrows.mk₂ (OpenRational.openRationalMayerVietorisFirst (X := TopCat.of M) U V 0)
        (OpenRational.openRationalMayerVietorisSecond (X := TopCat.of M) U V 0) :=
    ComposableArrows.homMk₂
      (ComplexManifoldCap.complexManifoldCompactSupportCap d (M := ↥(U ⊓ V)) p 0 hp)
      (MayerVietoris.poincareMayerVietorisMiddle d U V p 0 hp)
      (ComplexManifoldCap.complexManifoldCompactSupportCap d (M := ↥(U ⊔ V)) p 0 hp)
      (MayerVietoris.poincareMayerVietoris_first d U V p 0 hp)
      (MayerVietoris.poincareMayerVietoris_second d U V p 0 hp)
  have h : IsIso (ComposableArrows.app' φ 2) :=
    CategoryTheory.Abelian.isIso_of_epi_of_isIso φ
      (CompactSupportMayerVietoris.compactSupportMayerVietorisFirstSecondSequence_exact
        (X := TopCat.of M) U V p).exact_toComposableArrows
      (OpenRational.openRationalMayerVietoris_exact_middle (X := TopCat.of M) U V 0).exact_toComposableArrows
      (CompactSupportMayerVietoris.compactSupportMayerVietorisSecond_epi_of_isZero (X := TopCat.of M) U V p
        (hUV.cohomology_isZero (p + 1) (by omega)))
      (OpenRational.openRationalMayerVietorisSecond_zero_epi (X := TopCat.of M) U V)
      (by change Epi (ComplexManifoldCap.complexManifoldCompactSupportCap d (M := ↥(U ⊓ V)) p 0 hp); infer_instance)
      (by change IsIso (MayerVietoris.poincareMayerVietorisMiddle d U V p 0 hp); infer_instance)
  exact h

/-- The positive homological-degree five-lemma reduction. Its one explicit
premise is the equality of the actual connecting maps, with the exact sign
from the cap boundary formula. -/
theorem Property.HasCanonicalPoincareDuality.cap_sup_isIso_succ_of_boundary (U V : Opens M)
    (hU : Property.HasCanonicalPoincareDuality d U) (hV : Property.HasCanonicalPoincareDuality d V)
    (hUV : Property.HasCanonicalPoincareDuality d ↥(U ⊓ V))
    (p q : ℕ) (hpq : p + (q + 1) = 2 * d)
    (hboundary :
      ComplexManifoldCap.complexManifoldCompactSupportCap d (M := ↥(U ⊔ V)) p (q + 1) hpq ≫
          OpenRational.openRationalMayerVietorisBoundary (X := TopCat.of M) U V q =
        ((-1 : ℤ) ^ (p + 1)) •
          (CompactSupportMayerVietoris.compactSupportMayerVietorisBoundary (X := TopCat.of M) U V p ≫
            ComplexManifoldCap.complexManifoldCompactSupportCap d (M := ↥(U ⊓ V)) (p + 1) q (by omega))) :
    IsIso (ComplexManifoldCap.complexManifoldCompactSupportCap d (M := ↥(U ⊔ V)) p (q + 1) hpq) := by
  have hpq' : p + 1 + q = 2 * d := by omega
  let : IsIso (ComplexManifoldCap.complexManifoldCompactSupportCap d (M := ↥(U ⊓ V)) p (q + 1) hpq) :=
    hUV.cap_isIso p (q + 1) hpq
  let : IsIso (MayerVietoris.poincareMayerVietorisMiddle d U V p (q + 1) hpq) :=
    MayerVietoris.poincareMayerVietorisMiddle_isIso d U V hU hV p (q + 1) hpq
  let : IsIso (ComplexManifoldCap.complexManifoldCompactSupportCap d (M := ↥(U ⊓ V)) (p + 1) q hpq') :=
    hUV.cap_isIso (p + 1) q hpq'
  let : IsIso (MayerVietoris.poincareMayerVietorisMiddle d U V (p + 1) q hpq') :=
    MayerVietoris.poincareMayerVietorisMiddle_isIso d U V hU hV (p + 1) q hpq'
  exact SignedFiveLemma.isIso_of_signed_five_lemma
    (CompactSupportMayerVietoris.compactSupportMayerVietorisFirst (X := TopCat.of M) U V p)
    (CompactSupportMayerVietoris.compactSupportMayerVietorisSecond (X := TopCat.of M) U V p)
    (CompactSupportMayerVietoris.compactSupportMayerVietorisBoundary (X := TopCat.of M) U V p)
    (CompactSupportMayerVietoris.compactSupportMayerVietorisFirst (X := TopCat.of M) U V (p + 1))
    (OpenRational.openRationalMayerVietorisFirst (X := TopCat.of M) U V (q + 1))
    (OpenRational.openRationalMayerVietorisSecond (X := TopCat.of M) U V (q + 1))
    (OpenRational.openRationalMayerVietorisBoundary (X := TopCat.of M) U V q)
    (OpenRational.openRationalMayerVietorisFirst (X := TopCat.of M) U V q)
    (ComplexManifoldCap.complexManifoldCompactSupportCap d (M := ↥(U ⊓ V)) p (q + 1) hpq)
    (MayerVietoris.poincareMayerVietorisMiddle d U V p (q + 1) hpq)
    (ComplexManifoldCap.complexManifoldCompactSupportCap d (M := ↥(U ⊔ V)) p (q + 1) hpq)
    (ComplexManifoldCap.complexManifoldCompactSupportCap d (M := ↥(U ⊓ V)) (p + 1) q hpq')
    (MayerVietoris.poincareMayerVietorisMiddle d U V (p + 1) q hpq') (p + 1)
    (ComposableArrows.exact_of_δ₀
      ((CompactSupportMayerVietoris.compactSupportMayerVietorisSequence_exact (X := TopCat.of M) U V p).exact 0).exact_toComposableArrows
      (ComposableArrows.exact_of_δ₀
        ((CompactSupportMayerVietoris.compactSupportMayerVietorisSequence_exact (X := TopCat.of M) U V p).exact 1).exact_toComposableArrows
        ((CompactSupportMayerVietoris.compactSupportMayerVietorisSequence_exact (X := TopCat.of M) U V p).exact 2).exact_toComposableArrows))
    (ComposableArrows.exact_of_δ₀
      (OpenRational.openRationalMayerVietoris_exact_middle (X := TopCat.of M) U V (q + 1)).exact_toComposableArrows
      (ComposableArrows.exact_of_δ₀
        (OpenRational.openRationalMayerVietoris_exact_union (X := TopCat.of M) U V q).exact_toComposableArrows
        (OpenRational.openRationalMayerVietoris_exact_intersection (X := TopCat.of M) U V q).exact_toComposableArrows))
    (MayerVietoris.poincareMayerVietoris_first d U V p (q + 1) hpq)
    (MayerVietoris.poincareMayerVietoris_second d U V p (q + 1) hpq)
    hboundary
    (MayerVietoris.poincareMayerVietoris_first d U V (p + 1) q hpq')

/-- The full canonical Poincare-duality induction property is preserved
under a binary union of open submanifolds. All maps are the actual canonical
cap maps; the connecting-square identity is proved, not assumed. -/
theorem Property.HasCanonicalPoincareDuality.sup (U V : Opens M)
    (hU : Property.HasCanonicalPoincareDuality d U) (hV : Property.HasCanonicalPoincareDuality d V)
    (hUV : Property.HasCanonicalPoincareDuality d ↥(U ⊓ V)) :
    Property.HasCanonicalPoincareDuality d ↥(U ⊔ V) := by
  constructor
  · intro p q hpq
    cases q with
    | zero => exact Property.HasCanonicalPoincareDuality.cap_sup_isIso_zero d (M := M) U V hU hV hUV p hpq
    | succ q =>
      exact Property.HasCanonicalPoincareDuality.cap_sup_isIso_succ_of_boundary d (M := M) U V hU hV hUV p q hpq
        (CanonicalCapMayerVietoris.complexManifoldCap_mayerVietoris d (M := M) U V p q hpq)
  · intro p hp
    exact Property.HasCanonicalPoincareDuality.cohomology_isZero_sup d (M := M) U V hU hV hUV p hp

end

end OAI.AlgebraicTopology.Duality.Poincare
