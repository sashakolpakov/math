import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.PresheafExtendedScalars

/-! # Pushed Scalar Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PushedScalarNaturality

noncomputable section

/-! Changed-base scalar actions on section presheaves commute with actual module-sheaf morphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem pushedCoefficientScalarRingHom_natural
    {X Y : Scheme.{u}} {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (a : Y ⟶ X) (f : R →+* Γ(X, ⊤)) (q : B →+* Γ(Y, ⊤))
    {M N : Y.Modules} (e : M ⟶ N) (b : B) :
    Section.PresheafExtendedScalars.pushedCoefficientScalarRingHom a f M q b ≫
        (Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor f).map ((Scheme.Modules.pushforward a).map e) =
      (Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor f).map ((Scheme.Modules.pushforward a).map e) ≫
        Section.PresheafExtendedScalars.pushedCoefficientScalarRingHom a f N q b := by
  let F := Scheme.Modules.pushforward a ⋙ Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor f
  exact (F.map_comp (Global.ModuleScalars.globalModuleScalar M (q b)) e).symm.trans
    ((congrArg F.map (Global.ModuleScalars.globalModuleScalar_natural (q b) e)).trans
      (F.map_comp e (Global.ModuleScalars.globalModuleScalar N (q b))))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PushedScalarNaturality
