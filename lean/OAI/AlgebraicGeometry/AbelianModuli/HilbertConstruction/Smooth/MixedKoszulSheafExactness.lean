import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.MixedKoszulStalkExactness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.LineBundleCommonFrames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.StalkOpenRestriction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.PointStalkRegularParameters
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! # Mixed Koszul Sheaf Exactness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.MixedKoszulSheafExactness

noncomputable section

/-! On a smooth g-dimensional scheme over an algebraically closed
field, g line-bundle sections with finite common zero set give a mixed
Koszul complex exact in every negative degree as actual module sheaves.
At the common zeros regular parameters supply local acyclicity; away
from them a section supplies an actual contraction. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace IsLocalRing
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance smoothDimensionSourceLocal (g : ℕ) :
    IsZariskiLocalAtSource (@SmoothOfRelativeDimension g : MorphismProperty Scheme.{u}) :=
  HasRingHomProperty.instIsZariskiLocalAtSource
    (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension g))

local instance smoothMixedSheafPullbackAdditive {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (Scheme.Modules.pullback f).Additive := by
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (Scheme.Modules.pullback f)
  exact Functor.additive_of_preservesBinaryBiproducts _

theorem smoothMixedKoszul_sheaf_exact_negative
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) (g : ℕ) [SmoothOfRelativeDimension g p]
    (M : Line.Bundles.LineBundle X) (bs : List (LineBundleKoszulComplex.LineBundleSection X)) (hlen : bs.length = g)
    (hfinite : (MixedKoszulGeometricSupport.mixedSectionZeroSet bs).Finite) :
    ∀ i : ℤ, i < 0 → (LineBundleKoszulComplex.mixedLineBundleKoszulComplex M.sheaf bs).ExactAt i := by
  classical
  have : Smooth p := SmoothOfRelativeDimension.smooth g p
  let C := LineBundleKoszulComplex.mixedLineBundleKoszulComplex M.sheaf bs
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  intro i hi
  apply (Module.StalkOpenRestriction.moduleCochain_exactAt_iff_stalk C i).mpr
  intro x
  by_cases hx : x ∈ MixedKoszulGeometricSupport.mixedSectionZeroSet bs
  · obtain ⟨U, hxU, hU, ⟨eM⟩, frames⟩ := HilbertConstruction.Finite.LineBundleCommonFrames.mixedKoszul_common_affine_frame M bs x
    let y : U.toScheme := ⟨x, hxU⟩
    let q := U.ι ≫ p
    let cs := bs.map (MixedKoszulPullbackComplex.pullbackLineBundleSection U.ι)
    let : SmoothOfRelativeDimension g q :=
      IsZariskiLocalAtSource.comp (P := @SmoothOfRelativeDimension g) inferInstance U.ι
    have : Smooth q := SmoothOfRelativeDimension.smooth g q
    let : IsLocallyNoetherian U.toScheme := LocallyOfFiniteType.isLocallyNoetherian q
    let : JacobsonSpace U.toScheme := LocallyOfFiniteType.jacobsonSpace q
    have hfiniteU : (MixedKoszulGeometricSupport.mixedSectionZeroSet cs).Finite := by
      rw [MixedKoszulPullbackComplex.mixedSectionZeroSet_pullback]
      exact Set.Finite.preimage (fun a _ b _ h => U.ι.isEmbedding.injective h) hfinite
    have hyzero : y ∈ MixedKoszulGeometricSupport.mixedSectionZeroSet cs := by
      rw [MixedKoszulPullbackComplex.mixedSectionZeroSet_pullback]
      exact hx
    have hyclosed : IsClosed ({y} : Set U.toScheme) :=
      MixedKoszulGeometricSupport.finiteClosedSet_subset_closedPoints (MixedKoszulGeometricSupport.mixedSectionZeroSet cs)
        (MixedKoszulGeometricSupport.mixedSectionZeroSet_isClosed cs) hfiniteU hyzero
    let s := pointOfClosedPoint q y hyclosed
    have hs : s ≫ q = 𝟙 _ := pointOfClosedPoint_comp q y hyclosed
    have hparameters : ∃ ps : List (U.toScheme.presheaf.stalk y),
        Regular.SequenceBasic.RingTheory.Sequence.IsRegular (U.toScheme.presheaf.stalk y) ps ∧
        Regular.SequenceBasic.Ideal.ofList ps = maximalIdeal (U.toScheme.presheaf.stalk y) ∧ ps.length = g := by
      have hpoint : s (IsLocalRing.closedPoint K) = y := pointOfClosedPoint_apply q y hyclosed _
      exact (congrArg (fun z : U.toScheme => ∃ ps : List (U.toScheme.presheaf.stalk z),
        Regular.SequenceBasic.RingTheory.Sequence.IsRegular (U.toScheme.presheaf.stalk z) ps ∧
        Regular.SequenceBasic.Ideal.ofList ps = maximalIdeal (U.toScheme.presheaf.stalk z) ∧ ps.length = g)
        hpoint).mp (Rational.PointStalkRegularParameters.rationalPoint_stalk_regular_parameters q g s hs)
    obtain ⟨ps, hreg, hgen, hps⟩ := hparameters
    have hlength : cs.length = ps.length := by simp only [cs, List.length_map, hlen, hps]
    have hexa := Framed.MixedKoszulStalkExactness.framedMixedKoszul_stalk_exact_negative y (M.pullback U.ι).sheaf eM
      cs frames hfiniteU ps hlength hreg hgen i hi
    let F := Module.StalkExactness.moduleStalkFunctor y
    let e := (F.mapHomologicalComplex (.up ℤ)).mapIso (MixedKoszulPullbackComplex.mixedKoszulPullbackIso U.ι M.sheaf bs)
    have hlocal : ((F.mapHomologicalComplex (.up ℤ)).obj
        (((Scheme.Modules.pullback U.ι).mapHomologicalComplex (.up ℤ)).obj C)).ExactAt i :=
      (exactAt_iff_of_quasiIsoAt e.hom i).mpr hexa
    exact (Module.StalkOpenRestriction.moduleCochain_pullback_stalk_exactAt_iff U.ι C y i).mp hlocal
  · obtain ⟨b, hb, hxb⟩ : ∃ b ∈ bs, x ∈ Ample.LineBundles.sectionNonvanishing b.2 := by
      by_contra hn
      apply hx
      change ∀ b ∈ bs, x ∉ Ample.LineBundles.sectionNonvanishing b.2
      intro b hb hxb
      exact hn ⟨b, hb, hxb⟩
    let U := Ample.LineBundles.sectionNonvanishing b.2
    let y : U.toScheme := ⟨x, hxb⟩
    have hframe : IsIso ((Scheme.Modules.pullback U.ι).map b.2) :=
      (Section.Nonvanishing.isIso_pullbackSection_iff U.ι b.2).mp inferInstance
    have hcontract := LineBundleKoszulComplex.mixedLineBundleKoszulComplex_pullback_contractible M.sheaf bs U.ι ⟨b, hb, hframe⟩
    have hacy := Module.ComplexLocalExactness.cochain_acyclic_of_contractible _ hcontract
    have hlocal : (((Module.StalkExactness.moduleStalkFunctor y).mapHomologicalComplex (.up ℤ)).obj
        (((Scheme.Modules.pullback U.ι).mapHomologicalComplex (.up ℤ)).obj C)).ExactAt i :=
      ShortComplex.Exact.map (hacy i) (Module.StalkExactness.moduleStalkFunctor y)
    exact (Module.StalkOpenRestriction.moduleCochain_pullback_stalk_exactAt_iff U.ι C y i).mp hlocal

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.MixedKoszulSheafExactness
