import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CoverSheafExistence
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Limits.Over

/-! # Fppf Sheaf Existence -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.FppfSheafExistence.Construction

noncomputable section

/-! Fppf sheaf sections over a Noetherian test scheme can be glued
using uniqueness only on Noetherian tests: the covering maps and their
pairwise pullbacks are locally of finite presentation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u w

set_option backward.isDefEq.respectTransparency false in
theorem noetherian_fppf_sheaf_nonempty_of_cover
    {S : Scheme.{u}} (P : (Over S)ᵒᵖ ⥤ Type w)
    (hP : Presheaf.IsSheaf (Scheme.fppfTopology.over S) P)
    (hsub : ∀ (U : Over S) [IsLocallyNoetherian U.left], Subsingleton (P.obj (op U)))
    (T : Over S) [IsLocallyNoetherian T.left]
    (R : Sieve T) (hR : R ∈ (Scheme.fppfTopology.over S) T)
    (hlocal : ∀ (U : Over S) [IsLocallyNoetherian U.left] (f : U ⟶ T),
      R f → Nonempty (P.obj (op U))) : Nonempty (P.obj (op T)) := by
  have : Scheme.fppfPrecoverage.HasIsos := by
    constructor
    intro X Y f _
    exact (Scheme.singleton_mem_precoverage_iff _ f).mpr
      ⟨f.surjective, inferInstance, inferInstance⟩
  have : Scheme.fppfPrecoverage.HasPullbacks := by
    dsimp only [Scheme.fppfPrecoverage]
    infer_instance
  let K := Scheme.fppfPrecoverage.comap (Over.forget S)
  have hJ : Scheme.fppfTopology.over S = K.toGrothendieck :=
    over_toGrothendieck_eq_toGrothendieck_comap_forget Scheme.fppfPrecoverage S
  obtain ⟨E, hE, hER⟩ :=
    K.mem_toGrothendieck_iff_of_isStableUnderComposition.mp (hJ ▸ hR)
  have hlfp {U : Over S} (f : U ⟶ T) (hf : E f) : LocallyOfFinitePresentation f.left := by
    have hE' : E.map (Over.forget S) ∈ Scheme.fppfPrecoverage T.left := hE
    exact (hE'.2 (E.map_map hf)).2
  apply CoverSheafExistence.Construction.sheaf_nonempty_of_cover_subsingleton_pullbacks (Scheme.fppfTopology.over S) P hP E
    (hJ.symm ▸ Precoverage.generate_mem_toGrothendieck hE)
  · intro U f hf
    have := hlfp f hf
    have : IsLocallyNoetherian U.left := LocallyOfFiniteType.isLocallyNoetherian f.left
    exact hlocal U f (hER U f hf)
  · intro U V f g hf hg
    have := hlfp f hf
    have : IsLocallyNoetherian U.left := LocallyOfFiniteType.isLocallyNoetherian f.left
    have := hlfp g hg
    have H : IsPullback (pullback.fst f g).left (pullback.snd f g).left f.left g.left :=
      Functor.map_isPullback (Over.forget S) (IsPullback.of_hasPullback f g)
    have : LocallyOfFinitePresentation (pullback.fst f g).left :=
      MorphismProperty.of_isPullback H.flip (hlfp g hg)
    have : IsLocallyNoetherian (pullback f g).left :=
      LocallyOfFiniteType.isLocallyNoetherian (pullback.fst f g).left
    exact hsub (pullback f g)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.FppfSheafExistence.Construction
