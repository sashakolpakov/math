import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FlasqueSheafCohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.AdditiveSheafRestrictionExactness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.InjectiveCokernelSequence

/-! # Injective Syzygy Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.InjectiveSyzygySections.ZariskiCohomology.FlasqueAcyclicity

noncomputable section

universe u
open _root_.CategoryTheory Limits Opposite _root_.TopologicalSpace _root_.AlgebraicGeometry

theorem openSheafPullback_isFlasque
    {X : Scheme.{u}} (U : X.Opens) (F : InjectiveSheafFlasqueness.ZariskiCohomology.FlasqueAcyclicity.AbSheaf X)
    [TopCat.Sheaf.IsFlasque F] :
    TopCat.Sheaf.IsFlasque ((Open.AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openSheafPullback U).obj F) := by
  constructor
  intro V W i
  change Epi (F.obj.map _)
  infer_instance

theorem subsingleton_H_X₃_of_shortExact
    {X : Scheme.{u}} {S : ShortComplex (InjectiveSheafFlasqueness.ZariskiCohomology.FlasqueAcyclicity.AbSheaf X)}
    (hS : S.ShortExact) (n : ℕ)
    (hmiddle : Subsingleton (CategoryTheory.Sheaf.H S.X₂ n))
    (hleft : Subsingleton (CategoryTheory.Sheaf.H S.X₁ (n + 1))) :
    Subsingleton (CategoryTheory.Sheaf.H S.X₃ n) := by
  let : Subsingleton (CategoryTheory.Sheaf.H S.X₂ n) := hmiddle
  let : Subsingleton (CategoryTheory.Sheaf.H S.X₁ (n + 1)) := hleft
  refine subsingleton_of_forall_eq 0 fun c ↦ ?_
  obtain ⟨y, hy⟩ := HilbertConstruction.Sheaf.CohomologyExact.SheafCohomologyExact.Cohomology.longSequence_exact₃_explicit
    hS n (n + 1) rfl c (Subsingleton.elim _ _)
  rw [Subsingleton.elim y 0, map_zero] at hy
  exact hy.symm

theorem openSheafPullback_injectiveCokernel_H_succ_subsingleton
    {X : Scheme.{u}} (U : X.Opens) (F : InjectiveSheafFlasqueness.ZariskiCohomology.FlasqueAcyclicity.AbSheaf X) (n : ℕ)
    (hF : Subsingleton
      (CategoryTheory.Sheaf.H ((Open.AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openSheafPullback U).obj F) (n + 2))) :
    Subsingleton (CategoryTheory.Sheaf.H
      ((Open.AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openSheafPullback U).obj (cokernel (Injective.ι F))) (n + 1)) := by
  let L := Open.AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openSheafPullback U
  let S := FlasqueSheafCohomology.ZariskiCohomology.FlasqueAcyclicity.injectiveCokernelSequence F
  let : PreservesFiniteLimits L := by
    dsimp [L]
    infer_instance
  let : PreservesFiniteColimits L := by
    dsimp [L]
    infer_instance
  let : L.PreservesZeroMorphisms := by infer_instance
  let : L.Additive := L.additive_of_preserves_binary_products
  have hS : S.ShortExact := FlasqueSheafCohomology.ZariskiCohomology.FlasqueAcyclicity.injectiveCokernelSequence_shortExact F
  have hSL : (S.map L).ShortExact :=
    ShortComplex.ShortExact.map_of_exact hS L
  have hI : TopCat.Sheaf.IsFlasque (Injective.under F) :=
    InjectiveSheafFlasqueness.ZariskiCohomology.FlasqueAcyclicity.injectiveSheaf_isFlasque (Injective.under F)
  let : TopCat.Sheaf.IsFlasque (Injective.under F) := hI
  let : TopCat.Sheaf.IsFlasque (L.obj (Injective.under F)) :=
    @openSheafPullback_isFlasque _ U (Injective.under F) hI
  have hmiddle : Subsingleton
      (CategoryTheory.Sheaf.H (L.obj (Injective.under F)) (n + 1)) :=
    FlasqueSheafCohomology.ZariskiCohomology.FlasqueAcyclicity.flasqueSheaf_H_succ_subsingleton _ n
  have hleft : Subsingleton
      (CategoryTheory.Sheaf.H (L.obj F) (n + 2)) := by
    exact hF
  exact subsingleton_H_X₃_of_shortExact hSL (n + 1) hmiddle hleft

theorem injectiveCokernel_app_surjective_of_pullback_HOne_subsingleton
    {R : CommRingCat.{u}} (F : InjectiveSheafFlasqueness.ZariskiCohomology.FlasqueAcyclicity.AbSheaf (Spec R))
    (U : (Spec R).Opens)
    (hF : Subsingleton
      (CategoryTheory.Sheaf.H ((Open.AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openSheafPullback U).obj F) 1)) :
    Function.Surjective
      ((cokernel.π (Injective.ι F)).hom.app (op U)) := by
  let L := Open.AdditiveSheafRestriction.ZariskiCohomology.LocalKilling.openSheafPullback U
  let S := FlasqueSheafCohomology.ZariskiCohomology.FlasqueAcyclicity.injectiveCokernelSequence F
  let : PreservesFiniteLimits L := by
    dsimp [L]
    infer_instance
  let : PreservesFiniteColimits L := by
    dsimp [L]
    infer_instance
  let : L.PreservesZeroMorphisms := by infer_instance
  let : L.Additive := L.additive_of_preserves_binary_products
  have hS : S.ShortExact := FlasqueSheafCohomology.ZariskiCohomology.FlasqueAcyclicity.injectiveCokernelSequence_shortExact F
  have hSL : (S.map L).ShortExact :=
    ShortComplex.ShortExact.map_of_exact hS L
  let : Subsingleton ((S.map L).X₁.H 1) := by
    change Subsingleton (CategoryTheory.Sheaf.H (L.obj F) 1)
    exact hF
  have hsurjective :=
    HilbertConstruction.Sheaf.CohomologyExact.SheafCohomologyExact.Cohomology.longSequence_surjective_of_subsingleton_H
      hSL (isTerminalTop : IsTerminal (⊤ : Opens (U : Scheme)))
  change Function.Surjective
    ((L.map (cokernel.π (Injective.ι F))).hom.app
      (op (⊤ : Opens (U : Scheme)))) at hsurjective
  change Function.Surjective
    ((cokernel.π (Injective.ι F)).hom.app
      (op (U.ι.isOpenEmbedding.functor.obj
        (⊤ : Opens (U : Scheme))))) at hsurjective
  have htop : U.ι.isOpenEmbedding.functor.obj
      (⊤ : Opens (U : Scheme)) = U := by
    ext x
    simp
  rw [htop] at hsurjective
  exact hsurjective

theorem affineSyzygyAppSurjective_of_pullback_H_succ_subsingleton
    {R : CommRingCat.{u}} (F : InjectiveSheafFlasqueness.ZariskiCohomology.FlasqueAcyclicity.AbSheaf (Spec R)) (n : ℕ)
    (hF : ∀ (U : (Spec R).Opens), IsAffineOpen U →
      ∀ k, k < n → Subsingleton
        (CategoryTheory.Sheaf.H
          ((U.ι.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).obj F)
            (k + 1))) :
    Open.InjectiveCokernelSequence.ZariskiCohomology.LocalKilling.AffineSyzygyAppSurjective F n := by
  induction n generalizing F with
  | zero => exact .zero F
  | succ n ih =>
      apply Open.InjectiveCokernelSequence.ZariskiCohomology.LocalKilling.AffineSyzygyAppSurjective.succ
      · intro U hU
        apply injectiveCokernel_app_surjective_of_pullback_HOne_subsingleton
        change Subsingleton (CategoryTheory.Sheaf.H
          ((U.ι.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).obj F) 1)
        exact hF U hU 0 (Nat.zero_lt_succ n)
      · apply ih
        intro U hU k hk
        apply openSheafPullback_injectiveCokernel_H_succ_subsingleton
        change Subsingleton (CategoryTheory.Sheaf.H
          ((U.ι.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).obj F)
            (k + 2))
        exact hF U hU (k + 1) (Nat.succ_lt_succ hk)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.InjectiveSyzygySections.ZariskiCohomology.FlasqueAcyclicity
