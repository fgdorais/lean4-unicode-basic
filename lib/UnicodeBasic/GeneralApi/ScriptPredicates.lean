/-
Copyright © 2023-2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import UnicodeBasic.GeneralApi.Script
public import UnicodeBasicCommon.Types.Script

@[expose] public section


/-!
  This file uses lookup tables:
  `Script`.
-/

namespace Unicode

/-- Check if character is Adlam -/
def isAdlam (char : Char) : Bool := isScript (Script.mk Script.CodePoints.adlam) char
/-- Check if character is Ahom -/
def isAhom (char : Char) : Bool := isScript (Script.mk Script.CodePoints.ahom) char
/-- Check if character is Anatolian_Hieroglyphs -/
def isAnatolianHieroglyphs (char : Char) : Bool := isScript (Script.mk Script.CodePoints.anatolianHieroglyphs) char
/-- Check if character is Arabic -/
def isArabic (char : Char) : Bool := isScript (Script.mk Script.CodePoints.arabic) char
/-- Check if character is Armenian -/
def isArmenian (char : Char) : Bool := isScript (Script.mk Script.CodePoints.armenian) char
/-- Check if character is Avestan -/
def isAvestan (char : Char) : Bool := isScript (Script.mk Script.CodePoints.avestan) char
/-- Check if character is Balinese -/
def isBalinese (char : Char) : Bool := isScript (Script.mk Script.CodePoints.balinese) char
/-- Check if character is Bamum -/
def isBamum (char : Char) : Bool := isScript (Script.mk Script.CodePoints.bamum) char
/-- Check if character is Bassa_Vah -/
def isBassaVah (char : Char) : Bool := isScript (Script.mk Script.CodePoints.bassaVah) char
/-- Check if character is Batak -/
def isBatak (char : Char) : Bool := isScript (Script.mk Script.CodePoints.batak) char
/-- Check if character is Bengali -/
def isBengali (char : Char) : Bool := isScript (Script.mk Script.CodePoints.bengali) char
/-- Check if character is Beria_Erfe -/
def isBeriaErfe (char : Char) : Bool := isScript (Script.mk Script.CodePoints.beriaErfe) char
/-- Check if character is Bhaiksuki -/
def isBhaiksuki (char : Char) : Bool := isScript (Script.mk Script.CodePoints.bhaiksuki) char
/-- Check if character is Bopomofo -/
def isBopomofo (char : Char) : Bool := isScript (Script.mk Script.CodePoints.bopomofo) char
/-- Check if character is Brahmi -/
def isBrahmi (char : Char) : Bool := isScript (Script.mk Script.CodePoints.brahmi) char
/-- Check if character is Braille -/
def isBraille (char : Char) : Bool := isScript (Script.mk Script.CodePoints.braille) char
/-- Check if character is Buginese -/
def isBuginese (char : Char) : Bool := isScript (Script.mk Script.CodePoints.buginese) char
/-- Check if character is Buhid -/
def isBuhid (char : Char) : Bool := isScript (Script.mk Script.CodePoints.buhid) char
/-- Check if character is Canadian_Aboriginal -/
def isCanadianAboriginal (char : Char) : Bool := isScript (Script.mk Script.CodePoints.canadianAboriginal) char
/-- Check if character is Carian -/
def isCarian (char : Char) : Bool := isScript (Script.mk Script.CodePoints.carian) char
/-- Check if character is Caucasian_Albanian -/
def isCaucasianAlbanian (char : Char) : Bool := isScript (Script.mk Script.CodePoints.caucasianAlbanian) char
/-- Check if character is Chakma -/
def isChakma (char : Char) : Bool := isScript (Script.mk Script.CodePoints.chakma) char
/-- Check if character is Cham -/
def isCham (char : Char) : Bool := isScript (Script.mk Script.CodePoints.cham) char
/-- Check if character is Cherokee -/
def isCherokee (char : Char) : Bool := isScript (Script.mk Script.CodePoints.cherokee) char
/-- Check if character is Chorasmian -/
def isChorasmian (char : Char) : Bool := isScript (Script.mk Script.CodePoints.chorasmian) char
/-- Check if character is Common -/
def isCommon (char : Char) : Bool := isScript (Script.mk Script.CodePoints.common) char
/-- Check if character is Coptic -/
def isCoptic (char : Char) : Bool := isScript (Script.mk Script.CodePoints.coptic) char
/-- Check if character is Cuneiform -/
def isCuneiform (char : Char) : Bool := isScript (Script.mk Script.CodePoints.cuneiform) char
/-- Check if character is Cypriot -/
def isCypriot (char : Char) : Bool := isScript (Script.mk Script.CodePoints.cypriot) char
/-- Check if character is Cypro_Minoan -/
def isCyproMinoan (char : Char) : Bool := isScript (Script.mk Script.CodePoints.cyproMinoan) char
/-- Check if character is Cyrillic -/
def isCyrillic (char : Char) : Bool := isScript (Script.mk Script.CodePoints.cyrillic) char
/-- Check if character is Deseret -/
def isDeseret (char : Char) : Bool := isScript (Script.mk Script.CodePoints.deseret) char
/-- Check if character is Devanagari -/
def isDevanagari (char : Char) : Bool := isScript (Script.mk Script.CodePoints.devanagari) char
/-- Check if character is Dives_Akuru -/
def isDivesAkuru (char : Char) : Bool := isScript (Script.mk Script.CodePoints.divesAkuru) char
/-- Check if character is Dogra -/
def isDogra (char : Char) : Bool := isScript (Script.mk Script.CodePoints.dogra) char
/-- Check if character is Duployan -/
def isDuployan (char : Char) : Bool := isScript (Script.mk Script.CodePoints.duployan) char
/-- Check if character is Egyptian_Hieroglyphs -/
def isEgyptianHieroglyphs (char : Char) : Bool := isScript (Script.mk Script.CodePoints.egyptianHieroglyphs) char
/-- Check if character is Elbasan -/
def isElbasan (char : Char) : Bool := isScript (Script.mk Script.CodePoints.elbasan) char
/-- Check if character is Elymaic -/
def isElymaic (char : Char) : Bool := isScript (Script.mk Script.CodePoints.elymaic) char
/-- Check if character is Ethiopic -/
def isEthiopic (char : Char) : Bool := isScript (Script.mk Script.CodePoints.ethiopic) char
/-- Check if character is Garay -/
def isGaray (char : Char) : Bool := isScript (Script.mk Script.CodePoints.garay) char
/-- Check if character is Georgian -/
def isGeorgian (char : Char) : Bool := isScript (Script.mk Script.CodePoints.georgian) char
/-- Check if character is Glagolitic -/
def isGlagolitic (char : Char) : Bool := isScript (Script.mk Script.CodePoints.glagolitic) char
/-- Check if character is Gothic -/
def isGothic (char : Char) : Bool := isScript (Script.mk Script.CodePoints.gothic) char
/-- Check if character is Grantha -/
def isGrantha (char : Char) : Bool := isScript (Script.mk Script.CodePoints.grantha) char
/-- Check if character is Greek -/
def isGreek (char : Char) : Bool := isScript (Script.mk Script.CodePoints.greek) char
/-- Check if character is Gujarati -/
def isGujarati (char : Char) : Bool := isScript (Script.mk Script.CodePoints.gujarati) char
/-- Check if character is Gunjala_Gondi -/
def isGunjalaGondi (char : Char) : Bool := isScript (Script.mk Script.CodePoints.gunjalaGondi) char
/-- Check if character is Gurmukhi -/
def isGurmukhi (char : Char) : Bool := isScript (Script.mk Script.CodePoints.gurmukhi) char
/-- Check if character is Gurung_Khema -/
def isGurungKhema (char : Char) : Bool := isScript (Script.mk Script.CodePoints.gurungKhema) char
/-- Check if character is Han -/
def isHan (char : Char) : Bool := isScript (Script.mk Script.CodePoints.han) char
/-- Check if character is Hangul -/
def isHangul (char : Char) : Bool := isScript (Script.mk Script.CodePoints.hangul) char
/-- Check if character is Hanifi_Rohingya -/
def isHanifiRohingya (char : Char) : Bool := isScript (Script.mk Script.CodePoints.hanifiRohingya) char
/-- Check if character is Hanunoo -/
def isHanunoo (char : Char) : Bool := isScript (Script.mk Script.CodePoints.hanunoo) char
/-- Check if character is Hatran -/
def isHatran (char : Char) : Bool := isScript (Script.mk Script.CodePoints.hatran) char
/-- Check if character is Hebrew -/
def isHebrew (char : Char) : Bool := isScript (Script.mk Script.CodePoints.hebrew) char
/-- Check if character is Hiragana -/
def isHiragana (char : Char) : Bool := isScript (Script.mk Script.CodePoints.hiragana) char
/-- Check if character is Imperial_Aramaic -/
def isImperialAramaic (char : Char) : Bool := isScript (Script.mk Script.CodePoints.imperialAramaic) char
/-- Check if character is Inherited -/
def isInherited (char : Char) : Bool := isScript (Script.mk Script.CodePoints.inherited) char
/-- Check if character is Inscriptional_Pahlavi -/
def isInscriptionalPahlavi (char : Char) : Bool := isScript (Script.mk Script.CodePoints.inscriptionalPahlavi) char
/-- Check if character is Inscriptional_Parthian -/
def isInscriptionalParthian (char : Char) : Bool := isScript (Script.mk Script.CodePoints.inscriptionalParthian) char
/-- Check if character is Javanese -/
def isJavanese (char : Char) : Bool := isScript (Script.mk Script.CodePoints.javanese) char
/-- Check if character is Kaithi -/
def isKaithi (char : Char) : Bool := isScript (Script.mk Script.CodePoints.kaithi) char
/-- Check if character is Kannada -/
def isKannada (char : Char) : Bool := isScript (Script.mk Script.CodePoints.kannada) char
/-- Check if character is Katakana -/
def isKatakana (char : Char) : Bool := isScript (Script.mk Script.CodePoints.katakana) char
/-- Check if character is Katakana_Or_Hiragana -/
def isKatakanaOrHiragana (char : Char) : Bool := isScript (Script.mk Script.CodePoints.katakanaOrHiragana) char
/-- Check if character is Kawi -/
def isKawi (char : Char) : Bool := isScript (Script.mk Script.CodePoints.kawi) char
/-- Check if character is Kayah_Li -/
def isKayahLi (char : Char) : Bool := isScript (Script.mk Script.CodePoints.kayahLi) char
/-- Check if character is Kharoshthi -/
def isKharoshthi (char : Char) : Bool := isScript (Script.mk Script.CodePoints.kharoshthi) char
/-- Check if character is Khitan_Small_Script -/
def isKhitanSmallScript (char : Char) : Bool := isScript (Script.mk Script.CodePoints.khitanSmallScript) char
/-- Check if character is Khmer -/
def isKhmer (char : Char) : Bool := isScript (Script.mk Script.CodePoints.khmer) char
/-- Check if character is Khojki -/
def isKhojki (char : Char) : Bool := isScript (Script.mk Script.CodePoints.khojki) char
/-- Check if character is Khudawadi -/
def isKhudawadi (char : Char) : Bool := isScript (Script.mk Script.CodePoints.khudawadi) char
/-- Check if character is Kirat_Rai -/
def isKiratRai (char : Char) : Bool := isScript (Script.mk Script.CodePoints.kiratRai) char
/-- Check if character is Lao -/
def isLao (char : Char) : Bool := isScript (Script.mk Script.CodePoints.lao) char
/-- Check if character is Latin -/
def isLatin (char : Char) : Bool := isScript (Script.mk Script.CodePoints.latin) char
/-- Check if character is Lepcha -/
def isLepcha (char : Char) : Bool := isScript (Script.mk Script.CodePoints.lepcha) char
/-- Check if character is Limbu -/
def isLimbu (char : Char) : Bool := isScript (Script.mk Script.CodePoints.limbu) char
/-- Check if character is Linear_A -/
def isLinearA (char : Char) : Bool := isScript (Script.mk Script.CodePoints.linearA) char
/-- Check if character is Linear_B -/
def isLinearB (char : Char) : Bool := isScript (Script.mk Script.CodePoints.linearB) char
/-- Check if character is Lisu -/
def isLisu (char : Char) : Bool := isScript (Script.mk Script.CodePoints.lisu) char
/-- Check if character is Lycian -/
def isLycian (char : Char) : Bool := isScript (Script.mk Script.CodePoints.lycian) char
/-- Check if character is Lydian -/
def isLydian (char : Char) : Bool := isScript (Script.mk Script.CodePoints.lydian) char
/-- Check if character is Mahajani -/
def isMahajani (char : Char) : Bool := isScript (Script.mk Script.CodePoints.mahajani) char
/-- Check if character is Makasar -/
def isMakasar (char : Char) : Bool := isScript (Script.mk Script.CodePoints.makasar) char
/-- Check if character is Malayalam -/
def isMalayalam (char : Char) : Bool := isScript (Script.mk Script.CodePoints.malayalam) char
/-- Check if character is Mandaic -/
def isMandaic (char : Char) : Bool := isScript (Script.mk Script.CodePoints.mandaic) char
/-- Check if character is Manichaean -/
def isManichaean (char : Char) : Bool := isScript (Script.mk Script.CodePoints.manichaean) char
/-- Check if character is Marchen -/
def isMarchen (char : Char) : Bool := isScript (Script.mk Script.CodePoints.marchen) char
/-- Check if character is Masaram_Gondi -/
def isMasaramGondi (char : Char) : Bool := isScript (Script.mk Script.CodePoints.masaramGondi) char
/-- Check if character is Medefaidrin -/
def isMedefaidrin (char : Char) : Bool := isScript (Script.mk Script.CodePoints.medefaidrin) char
/-- Check if character is Meetei_Mayek -/
def isMeeteiMayek (char : Char) : Bool := isScript (Script.mk Script.CodePoints.meeteiMayek) char
/-- Check if character is Mende_Kikakui -/
def isMendeKikakui (char : Char) : Bool := isScript (Script.mk Script.CodePoints.mendeKikakui) char
/-- Check if character is Meroitic_Cursive -/
def isMeroiticCursive (char : Char) : Bool := isScript (Script.mk Script.CodePoints.meroiticCursive) char
/-- Check if character is Meroitic_Hieroglyphs -/
def isMeroiticHieroglyphs (char : Char) : Bool := isScript (Script.mk Script.CodePoints.meroiticHieroglyphs) char
/-- Check if character is Miao -/
def isMiao (char : Char) : Bool := isScript (Script.mk Script.CodePoints.miao) char
/-- Check if character is Modi -/
def isModi (char : Char) : Bool := isScript (Script.mk Script.CodePoints.modi) char
/-- Check if character is Mongolian -/
def isMongolian (char : Char) : Bool := isScript (Script.mk Script.CodePoints.mongolian) char
/-- Check if character is Mro -/
def isMro (char : Char) : Bool := isScript (Script.mk Script.CodePoints.mro) char
/-- Check if character is Multani -/
def isMultani (char : Char) : Bool := isScript (Script.mk Script.CodePoints.multani) char
/-- Check if character is Myanmar -/
def isMyanmar (char : Char) : Bool := isScript (Script.mk Script.CodePoints.myanmar) char
/-- Check if character is Nabataean -/
def isNabataean (char : Char) : Bool := isScript (Script.mk Script.CodePoints.nabataean) char
/-- Check if character is Nag_Mundari -/
def isNagMundari (char : Char) : Bool := isScript (Script.mk Script.CodePoints.nagMundari) char
/-- Check if character is Nandinagari -/
def isNandinagari (char : Char) : Bool := isScript (Script.mk Script.CodePoints.nandinagari) char
/-- Check if character is New_Tai_Lue -/
def isNewTaiLue (char : Char) : Bool := isScript (Script.mk Script.CodePoints.newTaiLue) char
/-- Check if character is Newa -/
def isNewa (char : Char) : Bool := isScript (Script.mk Script.CodePoints.newa) char
/-- Check if character is Nko -/
def isNko (char : Char) : Bool := isScript (Script.mk Script.CodePoints.nko) char
/-- Check if character is Nushu -/
def isNushu (char : Char) : Bool := isScript (Script.mk Script.CodePoints.nushu) char
/-- Check if character is Nyiakeng_Puachue_Hmong -/
def isNyiakengPuachueHmong (char : Char) : Bool := isScript (Script.mk Script.CodePoints.nyiakengPuachueHmong) char
/-- Check if character is Ogham -/
def isOgham (char : Char) : Bool := isScript (Script.mk Script.CodePoints.ogham) char
/-- Check if character is Ol_Chiki -/
def isOlChiki (char : Char) : Bool := isScript (Script.mk Script.CodePoints.olChiki) char
/-- Check if character is Ol_Onal -/
def isOlOnal (char : Char) : Bool := isScript (Script.mk Script.CodePoints.olOnal) char
/-- Check if character is Old_Hungarian -/
def isOldHungarian (char : Char) : Bool := isScript (Script.mk Script.CodePoints.oldHungarian) char
/-- Check if character is Old_Italic -/
def isOldItalic (char : Char) : Bool := isScript (Script.mk Script.CodePoints.oldItalic) char
/-- Check if character is Old_North_Arabian -/
def isOldNorthArabian (char : Char) : Bool := isScript (Script.mk Script.CodePoints.oldNorthArabian) char
/-- Check if character is Old_Permic -/
def isOldPermic (char : Char) : Bool := isScript (Script.mk Script.CodePoints.oldPermic) char
/-- Check if character is Old_Persian -/
def isOldPersian (char : Char) : Bool := isScript (Script.mk Script.CodePoints.oldPersian) char
/-- Check if character is Old_Sogdian -/
def isOldSogdian (char : Char) : Bool := isScript (Script.mk Script.CodePoints.oldSogdian) char
/-- Check if character is Old_South_Arabian -/
def isOldSouthArabian (char : Char) : Bool := isScript (Script.mk Script.CodePoints.oldSouthArabian) char
/-- Check if character is Old_Turkic -/
def isOldTurkic (char : Char) : Bool := isScript (Script.mk Script.CodePoints.oldTurkic) char
/-- Check if character is Old_Uyghur -/
def isOldUyghur (char : Char) : Bool := isScript (Script.mk Script.CodePoints.oldUyghur) char
/-- Check if character is Oriya -/
def isOriya (char : Char) : Bool := isScript (Script.mk Script.CodePoints.oriya) char
/-- Check if character is Osage -/
def isOsage (char : Char) : Bool := isScript (Script.mk Script.CodePoints.osage) char
/-- Check if character is Osmanya -/
def isOsmanya (char : Char) : Bool := isScript (Script.mk Script.CodePoints.osmanya) char
/-- Check if character is Pahawh_Hmong -/
def isPahawhHmong (char : Char) : Bool := isScript (Script.mk Script.CodePoints.pahawhHmong) char
/-- Check if character is Palmyrene -/
def isPalmyrene (char : Char) : Bool := isScript (Script.mk Script.CodePoints.palmyrene) char
/-- Check if character is Pau_Cin_Hau -/
def isPauCinHau (char : Char) : Bool := isScript (Script.mk Script.CodePoints.pauCinHau) char
/-- Check if character is Phags_Pa -/
def isPhagsPa (char : Char) : Bool := isScript (Script.mk Script.CodePoints.phagsPa) char
/-- Check if character is Phoenician -/
def isPhoenician (char : Char) : Bool := isScript (Script.mk Script.CodePoints.phoenician) char
/-- Check if character is Psalter_Pahlavi -/
def isPsalterPahlavi (char : Char) : Bool := isScript (Script.mk Script.CodePoints.psalterPahlavi) char
/-- Check if character is Rejang -/
def isRejang (char : Char) : Bool := isScript (Script.mk Script.CodePoints.rejang) char
/-- Check if character is Runic -/
def isRunic (char : Char) : Bool := isScript (Script.mk Script.CodePoints.runic) char
/-- Check if character is Samaritan -/
def isSamaritan (char : Char) : Bool := isScript (Script.mk Script.CodePoints.samaritan) char
/-- Check if character is Saurashtra -/
def isSaurashtra (char : Char) : Bool := isScript (Script.mk Script.CodePoints.saurashtra) char
/-- Check if character is Sharada -/
def isSharada (char : Char) : Bool := isScript (Script.mk Script.CodePoints.sharada) char
/-- Check if character is Shavian -/
def isShavian (char : Char) : Bool := isScript (Script.mk Script.CodePoints.shavian) char
/-- Check if character is Siddham -/
def isSiddham (char : Char) : Bool := isScript (Script.mk Script.CodePoints.siddham) char
/-- Check if character is Sidetic -/
def isSidetic (char : Char) : Bool := isScript (Script.mk Script.CodePoints.sidetic) char
/-- Check if character is SignWriting -/
def isSignWriting (char : Char) : Bool := isScript (Script.mk Script.CodePoints.signwriting) char
/-- Check if character is Sinhala -/
def isSinhala (char : Char) : Bool := isScript (Script.mk Script.CodePoints.sinhala) char
/-- Check if character is Sogdian -/
def isSogdian (char : Char) : Bool := isScript (Script.mk Script.CodePoints.sogdian) char
/-- Check if character is Sora_Sompeng -/
def isSoraSompeng (char : Char) : Bool := isScript (Script.mk Script.CodePoints.soraSompeng) char
/-- Check if character is Soyombo -/
def isSoyombo (char : Char) : Bool := isScript (Script.mk Script.CodePoints.soyombo) char
/-- Check if character is Sundanese -/
def isSundanese (char : Char) : Bool := isScript (Script.mk Script.CodePoints.sundanese) char
/-- Check if character is Sunuwar -/
def isSunuwar (char : Char) : Bool := isScript (Script.mk Script.CodePoints.sunuwar) char
/-- Check if character is Syloti_Nagri -/
def isSylotiNagri (char : Char) : Bool := isScript (Script.mk Script.CodePoints.sylotiNagri) char
/-- Check if character is Syriac -/
def isSyriac (char : Char) : Bool := isScript (Script.mk Script.CodePoints.syriac) char
/-- Check if character is Tagalog -/
def isTagalog (char : Char) : Bool := isScript (Script.mk Script.CodePoints.tagalog) char
/-- Check if character is Tagbanwa -/
def isTagbanwa (char : Char) : Bool := isScript (Script.mk Script.CodePoints.tagbanwa) char
/-- Check if character is Tai_Le -/
def isTaiLe (char : Char) : Bool := isScript (Script.mk Script.CodePoints.taiLe) char
/-- Check if character is Tai_Tham -/
def isTaiTham (char : Char) : Bool := isScript (Script.mk Script.CodePoints.taiTham) char
/-- Check if character is Tai_Viet -/
def isTaiViet (char : Char) : Bool := isScript (Script.mk Script.CodePoints.taiViet) char
/-- Check if character is Tai_Yo -/
def isTaiYo (char : Char) : Bool := isScript (Script.mk Script.CodePoints.taiYo) char
/-- Check if character is Takri -/
def isTakri (char : Char) : Bool := isScript (Script.mk Script.CodePoints.takri) char
/-- Check if character is Tamil -/
def isTamil (char : Char) : Bool := isScript (Script.mk Script.CodePoints.tamil) char
/-- Check if character is Tangsa -/
def isTangsa (char : Char) : Bool := isScript (Script.mk Script.CodePoints.tangsa) char
/-- Check if character is Tangut -/
def isTangut (char : Char) : Bool := isScript (Script.mk Script.CodePoints.tangut) char
/-- Check if character is Telugu -/
def isTelugu (char : Char) : Bool := isScript (Script.mk Script.CodePoints.telugu) char
/-- Check if character is Thaana -/
def isThaana (char : Char) : Bool := isScript (Script.mk Script.CodePoints.thaana) char
/-- Check if character is Thai -/
def isThai (char : Char) : Bool := isScript (Script.mk Script.CodePoints.thai) char
/-- Check if character is Tibetan -/
def isTibetan (char : Char) : Bool := isScript (Script.mk Script.CodePoints.tibetan) char
/-- Check if character is Tifinagh -/
def isTifinagh (char : Char) : Bool := isScript (Script.mk Script.CodePoints.tifinagh) char
/-- Check if character is Tirhuta -/
def isTirhuta (char : Char) : Bool := isScript (Script.mk Script.CodePoints.tirhuta) char
/-- Check if character is Todhri -/
def isTodhri (char : Char) : Bool := isScript (Script.mk Script.CodePoints.todhri) char
/-- Check if character is Tolong_Siki -/
def isTolongSiki (char : Char) : Bool := isScript (Script.mk Script.CodePoints.tolongSiki) char
/-- Check if character is Toto -/
def isToto (char : Char) : Bool := isScript (Script.mk Script.CodePoints.toto) char
/-- Check if character is Tulu_Tigalari -/
def isTuluTigalari (char : Char) : Bool := isScript (Script.mk Script.CodePoints.tuluTigalari) char
/-- Check if character is Ugaritic -/
def isUgaritic (char : Char) : Bool := isScript (Script.mk Script.CodePoints.ugaritic) char
/-- Check if character is Unknown -/
def isUnknown (char : Char) : Bool := isMaybeUnknownScript (MaybeUnknownScript.mk Script.CodePoints.unknown) char
/-- Check if character is Vai -/
def isVai (char : Char) : Bool := isScript (Script.mk Script.CodePoints.vai) char
/-- Check if character is Vithkuqi -/
def isVithkuqi (char : Char) : Bool := isScript (Script.mk Script.CodePoints.vithkuqi) char
/-- Check if character is Wancho -/
def isWancho (char : Char) : Bool := isScript (Script.mk Script.CodePoints.wancho) char
/-- Check if character is Warang_Citi -/
def isWarangCiti (char : Char) : Bool := isScript (Script.mk Script.CodePoints.warangCiti) char
/-- Check if character is Yezidi -/
def isYezidi (char : Char) : Bool := isScript (Script.mk Script.CodePoints.yezidi) char
/-- Check if character is Yi -/
def isYi (char : Char) : Bool := isScript (Script.mk Script.CodePoints.yi) char
/-- Check if character is Zanabazar_Square -/
def isZanabazarSquare (char : Char) : Bool := isScript (Script.mk Script.CodePoints.zanabazarSquare) char

end Unicode
