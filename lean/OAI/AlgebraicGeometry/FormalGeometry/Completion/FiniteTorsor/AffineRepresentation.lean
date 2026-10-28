import OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.AffineDescent
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.SheafDescent
import OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.DescentComparison
import OAI.AlgebraicGeometry.FormalGeometry.Completion.CorepresentableEffectiveDescent

/-! # Affine Representation -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor

noncomputable section

/-!
# Completion: the descended algebra actually corepresents the finite torsor

For an affine faithfully flat trivialization, the finite étale descended
algebra corepresents the original torsor on the actual affine pro-étale site.
Both the algebra and section descent hypotheses are proved for these objects.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {R S : Type u} [CommRing R] [CommRing S]
  (f : R →+* S) (hf : WeaklyEtale (Spec.map (CommRingCat.ofHom f)))
  {ℓ n : ℕ} [NeZero (ℓ ^ n)]

variable (E : App.Construction.FiniteCoefficientExtension ℓ n (Spec (CommRingCat.of R)))
  (s : E.Fiber (Affine.CoverObject.Construction.affineCoverObject f hf)) (hflat : f.FaithfullyFlat)

/-- The actual descended finite étale algebra lies in the affine site category. -/
def App.Construction.FiniteCoefficientExtension.affineDescendedSiteAlgebra : ProEtale.Algebras.Construction.ProEtaleAlgebra R := by
  have : Etale (E.affineDescendedProEt f hf s hflat).hom :=
    E.affineDescendedProEt_etale f hf s hflat
  exact ⟨E.affineDescendedAlgebra f hf s hflat, by
    change WeaklyEtale (E.affineDescendedProEt f hf s hflat).hom
    infer_instance⟩

/-- Recovery respects the canonical torsor coaction in the actual affine site. -/
def App.Construction.FiniteCoefficientExtension.affineDescendedSiteCoalgebraIso :
    (Comonad.comparison (ProEtale.AlgebraBaseChange.Construction.proEtaleAlgebraAdj f hf)).obj
      (E.affineDescendedSiteAlgebra f hf s hflat) ≅
    CorepresentableDescent.Construction.corepresentableDescentCoalgebra (ProEtale.AlgebraBaseChange.Construction.proEtaleAlgebraAdj f hf)
      (Affine.SiteValues.Construction.proEtaleAffineValues E.fiberPresheaf) (E.affineRestrictedCorepresentative f hf s) :=
  ProEtale.DescentComparison.Construction.proEtaleComparisonIso f hf (CommDescentObject.Construction.descendedCommAlgebraCounit f hflat
    (Affine.DescentData.Construction.affineRepresentativeCoalgebra f hf (Affine.SiteValues.Construction.proEtaleAffineValues E.fiberPresheaf)
      (E.affineRestrictedCorepresentative f hf s)))

/-- The descended finite étale algebra corepresents the actual torsor on affine site objects. -/
def App.Construction.FiniteCoefficientExtension.affineDescendedCorepresentative :
    (Affine.SiteValues.Construction.proEtaleAffineValues E.fiberPresheaf).CorepresentableBy
      (E.affineDescendedSiteAlgebra f hf s hflat) :=
  CorepresentableEffectiveDescent.Construction.descendedCorepresentative (ProEtale.AlgebraBaseChange.Construction.proEtaleAlgebraAdj f hf)
    (Affine.SiteValues.Construction.proEtaleAffineValues E.fiberPresheaf) (E.affineRestrictedCorepresentative f hf s)
    (ProEtale.DescentComparison.Construction.proEtaleComparisonFullyFaithful f hf hflat)
    (Affine.SheafDescent.Construction.proEtaleAffineSectionToDescent_bijective f hf hflat E.fiberSheaf)
    (E.affineDescendedSiteCoalgebraIso f hf s hflat)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor
