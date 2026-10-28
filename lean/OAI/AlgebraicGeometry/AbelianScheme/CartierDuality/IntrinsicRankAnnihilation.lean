import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RankAnnihilation
import OAI.AlgebraicGeometry.Picard.Homomorphisms.FiniteHopfPresentation
import OAI.AlgebraicGeometry.Picard.Homomorphisms.FiniteFrobeniusTorsion
import OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelGroup
import OAI.AlgebraicGeometry.Picard.Homomorphisms.FrobeniusKernelBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-! # Intrinsic Rank Annihilation -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.IntrinsicRankAnnihilation.Construction.NormCharacters

noncomputable section

/-!
# CartierDuality: finite-flat degree kills the actual scheme-theoretic kernel
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

/-- The finite-flat rank kills the entire finite commutative group
scheme over a field, including its infinitesimal structure. -/
theorem finiteGroup_power_rank (k : Type u) [Field k]
    (G : Grp (Over (Spec (.of k)))) [IsCommMonObj G.X]
    [IsFinite G.X.hom] [Flat G.X.hom] (s : Spec (.of k)) :
    (𝟙 G.X : G.X ⟶ G.X) ^ G.X.hom.finrank s = 1 := by
  obtain ⟨R, hR, hc, ⟨e⟩⟩ := Picard.Homomorphisms.FiniteHopfPresentation.Construction.finite_commutative_hopfPresentation k G
  have : Module.Finite k R := hR
  have : Coalgebra.IsCocomm k R := hc
  let i : ((hopfSpec (.of k)).obj (.op R)).X ≅ G.X := (Grp.forget _).mapIso e
  have : IsIso i.hom.left := inferInstanceAs (IsIso ((Over.forget _).map i.hom))
  have hr : Module.finrank k R = G.X.hom.finrank s := by
    calc
      Module.finrank k R = (((hopfSpec (.of k)).obj (.op R)).X).hom.finrank s := by
        change _ = (Spec.map (CommRingCat.ofHom (algebraMap k R))).finrank s
        have h := Scheme.Hom.finrank_SpecMap_algebraMap k R (show PrimeSpectrum k from s)
        rw [Module.rankAtStalk_eq_finrank_of_free] at h
        exact h.symm
      _ = G.X.hom.finrank s := by
        rw [← i.hom.w, Scheme.Hom.finrank_comp_left_of_isIso]
  have hp : (𝟙 ((hopfSpec (.of k)).obj (.op R)).X) ^ Module.finrank k R = 1 := by
    have h := RankAnnihilation.Construction.NormCharacters.affineGroup_power_card k R (Module.finBasis k R)
    simp only [Fintype.card_fin] at h
    change (𝟙 ((hopfSpec (.of k)).obj (.op R)).X) ^ Module.finrank k R = 1 at h
    exact h
  have h := Picard.Homomorphisms.FiniteFrobeniusTorsion.Construction.group_power_of_iso e (Module.finrank k R) hp
  rwa [hr] at h

/-- The rank identity holds on points over every scheme over the field. -/
theorem finiteGroup_points_power_rank (k : Type u) [Field k]
    (G : Grp (Over (Spec (.of k)))) [IsCommMonObj G.X]
    [IsFinite G.X.hom] [Flat G.X.hom] (s : Spec (.of k))
    (T : Over (Spec (.of k))) (x : T ⟶ G.X) : x ^ G.X.hom.finrank s = 1 := by
  have h := congrArg (fun a : G.X ⟶ G.X => x ≫ a) (finiteGroup_power_rank k G s)
  simpa only [MonObj.comp_pow, Category.comp_id, MonObj.comp_one] using h

/-- The actual finite-flat degree of a homomorphism kills its kernel
on every test scheme, not only on geometric points. -/
theorem kernel_killed_by_degree (k : Type u) [Field k]
    {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B] [IsCommMonObj A]
    (f : A ⟶ B) [IsMonHom f] [IsFinite f.left] [Flat f.left]
    (s : Spec (.of k)) (T : Over (Spec (.of k))) (x : T ⟶ A) (hx : x ≫ f = 1) :
    x ^ f.left.finrank (η[B].left s) = 1 := by
  let sq : IsPullback (Picard.Homomorphisms.Kernel.Construction.kernelInclusion f).left (Picard.Homomorphisms.Kernel.Construction.kernelScheme f).hom f.left η[B].left :=
    (Picard.Homomorphisms.Kernel.Construction.kernelScheme_isPullback f).map (Over.forget (Spec (.of k)))
  have hfin : IsFinite (Picard.Homomorphisms.Kernel.Construction.kernelScheme f).hom :=
    MorphismProperty.of_isPullback (P := @IsFinite) sq (inferInstanceAs (IsFinite f.left))
  have hflat : Flat (Picard.Homomorphisms.Kernel.Construction.kernelScheme f).hom :=
    MorphismProperty.of_isPullback (P := @Flat) sq (inferInstanceAs (Flat f.left))
  let G : Grp (Over (Spec (.of k))) := Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)
  have : IsCommMonObj G.X := Picard.Homomorphisms.KernelGroup.Construction.kernelSchemeGroup_commutative f
  have : IsFinite G.X.hom := hfin
  have : Flat G.X.hom := hflat
  let z : T ⟶ G.X := Picard.Homomorphisms.FrobeniusKernelBaseChange.Construction.kernelLift f x hx
  have hz := finiteGroup_points_power_rank k G s T z
  have hr : G.X.hom.finrank s = f.left.finrank (η[B].left s) :=
    Scheme.Hom.finrank_of_isPullback _ _ _ _ sq s
  rw [hr] at hz
  calc
    x ^ f.left.finrank (η[B].left s) =
        (z ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion f) ^ f.left.finrank (η[B].left s) := by
      rw [show z ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion f = x from Picard.Homomorphisms.FrobeniusKernelBaseChange.Construction.kernelLift_inclusion f x hx]
    _ = (z ^ f.left.finrank (η[B].left s)) ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion f :=
      (MonObj.pow_comp z (f.left.finrank (η[B].left s)) (Picard.Homomorphisms.Kernel.Construction.kernelInclusion f)).symm
    _ = 1 := by rw [hz, MonObj.one_comp]

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.IntrinsicRankAnnihilation.Construction.NormCharacters
