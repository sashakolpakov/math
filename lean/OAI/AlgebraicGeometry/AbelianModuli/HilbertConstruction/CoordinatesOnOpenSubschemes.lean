import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.CoordinateValues

/-! # Coordinates On Open Subschemes -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoordinatesOnOpenSubschemes

noncomputable section

/-! Local coordinate identities stated directly over an open subset of the original scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {M : X.Modules}

/-- Express the local coordinate formula directly in `Γ(M,U)` using the
canonical isomorphism between functions on `U` and functions on its open subscheme. -/
theorem local_frameCoordinate_value_on_open (U : X.Opens)
    (s t : Line.Bundles.structureModule X ⟶ M) [IsIso (Ample.LineBundles.pullbackSection U.ι s)] :
    t.app U (1 : Γ(X, U)) =
      U.topIso.hom (Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection U.ι s) (Ample.LineBundles.pullbackSection U.ι t)) •
        s.app U (1 : Γ(X, U)) := by
  let j : U ⟶ U.ι ''ᵁ ⊤ := eqToHom U.ι_image_top.symm
  let c := Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection U.ι s) (Ample.LineBundles.pullbackSection U.ι t)
  have hv := Local.CoordinateValues.local_frameCoordinate_value U.ι s t
  have hmap := congrArg (fun z : Γ(M, U.ι ''ᵁ ⊤) => M.presheaf.map j.op z) hv
  have hm := M.map_smul j ((U.ι.appIso ⊤).inv c) (s.app (U.ι ''ᵁ ⊤) (1 : Γ(X, U.ι ''ᵁ ⊤)))
  have hs : M.presheaf.map j.op (s.app (U.ι ''ᵁ ⊤) (1 : Γ(X, U.ι ''ᵁ ⊤))) =
      s.app U (1 : Γ(X, U)) := (M.unitHomEquiv s).property j.op
  have ht : M.presheaf.map j.op (t.app (U.ι ''ᵁ ⊤) (1 : Γ(X, U.ι ''ᵁ ⊤))) =
      t.app U (1 : Γ(X, U)) := (M.unitHomEquiv t).property j.op
  have hc : X.presheaf.map j.op ((U.ι.appIso ⊤).inv c) = U.topIso.hom c := by
    rw [U.ι_appIso]
    rfl
  exact ht.symm.trans (hmap.trans (hm.trans
    (congrArg₂ (fun a : Γ(X, U) => fun z : Γ(M, U) => a • z) hc hs)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoordinatesOnOpenSubschemes
