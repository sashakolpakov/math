import OAI.AlgebraicGeometry.Resolution.Blowups.FlatPrincipalColon
import OAI.AlgebraicGeometry.Resolution.Blowups.Locally.PrincipalIdealSheaf
import OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.EqualityGluing
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.MonomialBoundaryAtlas

/-! # Principal Colon Flat Pullback -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Locally.PrincipalColonFlatPullback.Construction

noncomputable section

/-! Flat pullback preserves the native ideal quotient by a locally principal ideal. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem locallyPrincipal_noetherianIdealSheafColon_comap_flat
    {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (J K : X.IdealSheafData) (hK : PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf K) (q : Y ⟶ X) [Flat q] :
    (NoetherianIdealSheafColon.Construction.noetherianIdealSheafColon J K).comap q = NoetherianIdealSheafColon.Construction.noetherianIdealSheafColon (J.comap q) (K.comap q) := by
  choose U hmem c hc using fun y : Y => hK (q y)
  choose W hW hyW hsub using fun y : Y =>
    exists_isAffineOpen_mem_and_subset (U := q ⁻¹ᵁ (U y).1) (x := y) (hmem y)
  let V (y : Y) : Y.affineOpens := ⟨W y, hW y⟩
  have hcover : ⨆ y : Y, (V y).1 = ⊤ := by
    apply top_le_iff.mp
    intro y _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hyW y⟩
  apply IdealSheaf.EqualityGluing.Construction.idealSheaf_eq_of_openCover _ _ (Global.MonomialBoundaryAtlas.Construction.chosenAffineSpecCover V hcover).openCover
  intro y
  change Y at y
  let φ := (q.appLE (U y).1 (V y).1 (hsub y)).hom
  let : Algebra Γ(X, U y) Γ(Y, V y) := φ.toAlgebra
  let : Module.Flat Γ(X, U y) Γ(Y, V y) := q.flat_appLE (U y).2 (V y).2 (hsub y)
  have he : ((NoetherianIdealSheafColon.Construction.noetherianIdealSheafColon J K).comap q).ideal (V y) =
      (NoetherianIdealSheafColon.Construction.noetherianIdealSheafColon (J.comap q) (K.comap q)).ideal (V y) := by
    rw [IdealSheaf.AffinePullback.Construction.idealSheaf_comap_ideal_of_le _ q (U y) (V y) (hsub y),
      NoetherianIdealSheafColon.Construction.noetherianIdealSheafColon_ideal, hc y, NoetherianIdealSheafColon.Construction.noetherianIdealSheafColon_ideal,
      IdealSheaf.AffinePullback.Construction.idealSheaf_comap_ideal_of_le J q (U y) (V y) (hsub y),
      IdealSheaf.AffinePullback.Construction.idealSheaf_comap_ideal_of_le K q (U y) (V y) (hsub y), hc y,
      Ideal.map_span, Set.image_singleton]
    exact FlatPrincipalColon.Construction.flat_map_colon_principal (S := Γ(Y, V y)) (J.ideal (U y)) (c y)
  change ((NoetherianIdealSheafColon.Construction.noetherianIdealSheafColon J K).comap q).comap (V y).2.fromSpec =
    (NoetherianIdealSheafColon.Construction.noetherianIdealSheafColon (J.comap q) (K.comap q)).comap (V y).2.fromSpec
  rw [Affine.IdealSheafIdentification.Construction.idealSheaf_comap_fromSpec_eq_quotient_kernel, Affine.IdealSheafIdentification.Construction.idealSheaf_comap_fromSpec_eq_quotient_kernel, he]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Locally.PrincipalColonFlatPullback.Construction
