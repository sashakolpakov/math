import OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData

/-! # Symplectic Map Comp -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.SymplecticMapComp.Realization

/-! Scalar extension of symplectic matrices respects composition of ring homomorphisms. -/

open _root_.Matrix OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData

theorem mapSp_comp {ι R K L : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] [CommRing K] [CommRing L] (f : K →+* L) (e : R →+* K) (g : Theta.PoissonAutomorphyNormalizationData.Sp ι R) :
    Theta.PoissonAutomorphyNormalizationData.mapSp f (Theta.PoissonAutomorphyNormalizationData.mapSp e g) = Theta.PoissonAutomorphyNormalizationData.mapSp (f.comp e) g := by
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  rfl

end OAI.RepresentationTheory.Hecke.RadialDilation.SymplecticMapComp.Realization
