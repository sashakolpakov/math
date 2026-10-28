import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SchemeIdealModule

/-! # Section Iso -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Module.SectionIso.BundleCycles

noncomputable section

/-! # LineBundleCycles: actual sheaf isomorphisms give compatible linear isomorphisms on all sections -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X : Scheme.{0}} {M N : X.Modules} (e : M ≅ N)

def moduleSectionIso (U : X.Opens) : Γ(M, U) ≃ₗ[Γ(X, U)] Γ(N, U) where
  toFun m := e.hom.app U m
  invFun n := e.inv.app U n
  left_inv m := ConcreteCategory.congr_hom
    (congrArg (fun f : M ⟶ M => f.app U) e.hom_inv_id) m
  right_inv n := ConcreteCategory.congr_hom
    (congrArg (fun f : N ⟶ N => f.app U) e.inv_hom_id) n
  map_add' m n := (e.hom.app U).hom.map_add m n
  map_smul' r m := by simpa only [RingHom.id_apply] using e.hom.app_smul r m

theorem moduleSectionIso_naturality {U V : X.Opens} (h : U ≤ V) (m : Γ(M, V)) :
    moduleSectionIso e U (M.presheaf.map (homOfLE h).op m) =
      N.presheaf.map (homOfLE h).op (moduleSectionIso e V m) :=
  ConcreteCategory.congr_hom (e.hom.mapPresheaf.naturality (homOfLE h).op) m

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Module.SectionIso.BundleCycles
