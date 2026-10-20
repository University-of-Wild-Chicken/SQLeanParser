import SQLean.PostgresGrammar.Syntax

/-! Generated from PostgreSQL 16.15 at f0595c3d839debdb140903621c1b44a4f4d86256.
Regenerate with scripts/generate_postgresql_grammar.py; no upstream C actions execute. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
namespace SQLean.PostgresGrammar.Generated

private def shiftRow1024 : Array (Nat × Nat) := #[(310, 4261), (385, 4262)]

private def shiftRow1025 : Array (Nat × Nat) := #[(427, 4263)]

private def shiftRow1026 : Array (Nat × Nat) := #[(280, 4264)]

private def shiftRow1027 : Array (Nat × Nat) := #[(154, 4265)]

private def shiftRow1028 : Array (Nat × Nat) := #[(404, 4266)]

private def shiftRow1029 : Array (Nat × Nat) := #[(385, 4270)]

private def shiftRow1030 : Array (Nat × Nat) := #[(25, 4271), (139, 4272), (299, 1558), (354, 4273), (355, 4274), (385, 4275)]

private def shiftRow1031 : Array (Nat × Nat) := #[(377, 4281)]

private def shiftRow1032 : Array (Nat × Nat) := #[(154, 4282)]

private def shiftRow1033 : Array (Nat × Nat) := #[(154, 4284)]

private def shiftRow1034 : Array (Nat × Nat) := #[(377, 4290)]

private def shiftRow1035 : Array (Nat × Nat) := #[(377, 4291)]

private def shiftRow1036 : Array (Nat × Nat) := #[(241, 4292)]

private def shiftRow1037 : Array (Nat × Nat) := #[(514, 4296), (517, 4297)]

private def shiftRow1038 : Array (Nat × Nat) := #[(203, 4300)]

private def shiftRow1039 : Array (Nat × Nat) := #[(514, 4301), (517, 4302)]

private def shiftRow1040 : Array (Nat × Nat) := #[(503, 4303), (515, 4304)]

private def shiftRow1041 : Array (Nat × Nat) := #[(157, 4306)]

private def shiftRow1042 : Array (Nat × Nat) := #[(25, 1546), (31, 1547), (76, 1549), (132, 1550), (139, 1551), (142, 1552), (169, 1553), (205, 1554), (276, 1657), (280, 1556), (290, 1557), (299, 1558), (311, 1559), (350, 4309), (353, 1561), (354, 1562), (385, 4310), (454, 1564)]

private def shiftRow1043 : Array (Nat × Nat) := #[(295, 4315)]

private def shiftRow1044 : Array (Nat × Nat) := #[(311, 4316), (350, 4317), (385, 4318)]

private def shiftRow1045 : Array (Nat × Nat) := #[(25, 4319), (139, 4320), (311, 4321), (350, 4322), (385, 4323)]

private def shiftRow1046 : Array (Nat × Nat) := #[(3, 856), (20, 235), (21, 236), (22, 237), (23, 238), (24, 239), (25, 240), (26, 241), (27, 242), (28, 243), (30, 244), (31, 245), (32, 246), (40, 247), (41, 248), (42, 249), (44, 250), (45, 251), (46, 252), (47, 253), (48, 254), (49, 255), (50, 256), (51, 257), (53, 857), (54, 260), (55, 858), (56, 859), (58, 263), (59, 264), (60, 265), (61, 266), (62, 267), (63, 268), (64, 269), (67, 270), (68, 271), (69, 860), (70, 861), (71, 274), (73, 275), (74, 276), (75, 277), (76, 278), (79, 280), (81, 281), (82, 282), (83, 283), (84, 284), (85, 285), (86, 286), (87, 287), (88, 288), (89, 289), (90, 290), (92, 291), (93, 292), (94, 293), (95, 294), (96, 295), (97, 296), (99, 297), (100, 298), (101, 299), (102, 300), (106, 301), (110, 302), (111, 303), (112, 304), (113, 305), (114, 306), (115, 307), (116, 862), (117, 863), (118, 310), (120, 311), (122, 312), (123, 313), (124, 314), (125, 315), (126, 316), (127, 317), (128, 318), (130, 319), (131, 320), (132, 321), (133, 322), (136, 323), (137, 324), (138, 864), (139, 326), (140, 327), (142, 328), (143, 329), (144, 330), (146, 331), (147, 332), (148, 333), (150, 334), (151, 335), (152, 336), (153, 337), (155, 339), (156, 340), (157, 341), (158, 342), (161, 344), (163, 345), (164, 346), (165, 347), (166, 865), (167, 349), (169, 350), (171, 351), (172, 352), (173, 353), (175, 354), (176, 355), (177, 356), (178, 357), (179, 358), (181, 359), (185, 362), (186, 363), (188, 364), (189, 365), (190, 366), (191, 367), (192, 368), (193, 369), (194, 370), (195, 371), (196, 372), (197, 373), (199, 374), (200, 375), (201, 376), (202, 377), (203, 378), (204, 379), (205, 380), (206, 381), (208, 382), (209, 383), (211, 385), (212, 386), (213, 387), (214, 388), (215, 866), (216, 867), (218, 868), (220, 392), (221, 393), (222, 394), (223, 395), (224, 396), (225, 397), (230, 402), (231, 403), (232, 404), (233, 405), (234, 406), (235, 407), (238, 408), (240, 410), (241, 411), (242, 412), (244, 413), (245, 414), (246, 415), (249, 416), (250, 417), (251, 418), (252, 419), (253, 420), (254, 421), (255, 422), (256, 423), (257, 424), (258, 425), (259, 426), (260, 427), (261, 428), (262, 429), (263, 430), (264, 431), (265, 432), (266, 433), (267, 869), (268, 435), (269, 870), (270, 437), (271, 438), (272, 439), (273, 440), (274, 441), (275, 442), (276, 443), (277, 4325), (279, 446), (281, 447), (282, 448), (283, 449), (284, 450), (287, 452), (288, 871), (289, 454), (290, 455), (291, 456), (293, 457), (294, 458), (297, 459), (298, 460), (299, 461), (302, 462), (303, 463), (305, 465), (306, 466), (307, 467), (309, 469), (310, 470), (311, 471), (312, 472), (313, 473), (314, 474), (315, 475), (316, 476), (317, 477), (318, 478), (320, 479), (321, 480), (323, 482), (325, 484), (326, 485), (327, 486), (329, 487), (330, 488), (331, 489), (332, 490), (333, 491), (334, 492), (335, 493), (336, 494), (337, 495), (338, 496), (339, 872), (340, 498), (341, 499), (342, 500), (343, 501), (345, 502), (346, 503), (347, 504), (348, 505), (349, 506), (350, 507), (351, 508), (352, 509), (353, 510), (354, 511), (355, 512), (356, 513), (357, 514), (359, 515), (360, 516), (361, 517), (362, 518), (363, 519), (364, 520), (365, 521), (366, 522), (368, 524), (369, 525), (370, 526), (371, 527), (372, 528), (373, 529), (374, 530), (375, 531), (376, 532), (377, 533), (379, 534), (380, 535), (381, 536), (382, 537), (383, 538), (385, 539), (386, 540), (387, 873), (388, 542), (389, 543), (390, 544), (391, 545), (392, 546), (393, 874), (394, 548), (396, 549), (397, 550), (398, 551), (399, 552), (400, 553), (401, 554), (402, 555), (403, 556), (404, 557), (405, 558), (406, 559), (407, 560), (408, 561), (410, 563), (412, 564), (413, 565), (416, 566), (417, 567), (418, 568), (419, 569), (420, 570), (421, 571), (422, 572), (424, 573), (425, 875), (426, 876), (429, 576), (430, 577), (432, 579), (435, 581), (436, 582), (437, 583), (438, 584), (439, 585), (440, 586), (441, 587), (442, 588), (445, 589), (446, 590), (447, 591), (448, 592), (449, 593), (452, 594), (453, 595), (454, 596), (455, 597), (456, 598), (458, 877), (460, 601), (461, 602), (462, 603), (463, 604), (464, 605), (465, 606), (468, 607), (471, 608), (472, 609), (473, 610), (474, 611), (475, 612), (476, 613), (488, 625), (489, 626), (490, 627)]

private def shiftRow1047 : Array (Nat × Nat) := #[(514, 4327), (517, 4328)]

private def shiftRow1048 : Array (Nat × Nat) := #[(503, 4329)]

private def shiftRow1049 : Array (Nat × Nat) := #[(427, 4331)]

private def shiftRow1050 : Array (Nat × Nat) := #[(451, 4333)]

private def shiftRow1051 : Array (Nat × Nat) := #[(157, 4335)]

private def shiftRow1052 : Array (Nat × Nat) := #[(372, 4337)]

private def shiftRow1053 : Array (Nat × Nat) := #[(467, 4339)]

private def shiftRow1054 : Array (Nat × Nat) := #[(243, 4343)]

private def shiftRow1055 : Array (Nat × Nat) := #[(318, 4344)]

private def shiftRow1056 : Array (Nat × Nat) := #[(6, 694), (285, 4345)]

private def shiftRow1057 : Array (Nat × Nat) := #[(318, 4347)]

private def shiftRow1058 : Array (Nat × Nat) := #[(448, 4349)]

private def shiftRow1059 : Array (Nat × Nat) := #[(157, 4350)]

private def shiftRow1060 : Array (Nat × Nat) := #[(427, 4351)]

private def shiftRow1061 : Array (Nat × Nat) := #[(427, 4352)]

private def shiftRow1062 : Array (Nat × Nat) := #[(23, 2809), (252, 2810), (372, 4353), (418, 2811), (447, 2812), (472, 2813), (513, 2807)]

private def shiftRow1063 : Array (Nat × Nat) := #[(401, 4354)]

private def shiftRow1064 : Array (Nat × Nat) := #[(470, 1849), (517, 1947)]

private def shiftRow1065 : Array (Nat × Nat) := #[(310, 4358), (385, 4359)]

private def shiftRow1066 : Array (Nat × Nat) := #[(80, 2782), (91, 4360), (427, 4361)]

private def shiftRow1067 : Array (Nat × Nat) := #[(23, 2809), (252, 2810), (372, 4363), (418, 2811), (447, 2812), (472, 2813), (513, 2807)]

private def shiftRow1068 : Array (Nat × Nat) := #[(119, 4364), (168, 4365)]

private def shiftRow1069 : Array (Nat × Nat) := #[(87, 1881), (164, 4367)]

private def shiftRow1070 : Array (Nat × Nat) := #[(427, 4369)]

private def shiftRow1071 : Array (Nat × Nat) := #[(427, 4370)]

private def shiftRow1072 : Array (Nat × Nat) := #[(253, 4371)]

private def shiftRow1073 : Array (Nat × Nat) := #[(253, 4372)]

private def shiftRow1074 : Array (Nat × Nat) := #[(253, 4373)]

private def shiftRow1075 : Array (Nat × Nat) := #[(427, 4374)]

private def shiftRow1076 : Array (Nat × Nat) := #[(427, 4375)]

private def shiftRow1077 : Array (Nat × Nat) := #[(372, 4376)]

private def shiftRow1078 : Array (Nat × Nat) := #[(427, 4377)]

private def shiftRow1079 : Array (Nat × Nat) := #[(427, 4378)]

private def shiftRow1080 : Array (Nat × Nat) := #[(372, 4379)]

private def shiftRow1081 : Array (Nat × Nat) := #[(427, 4380)]

private def shiftRow1082 : Array (Nat × Nat) := #[(372, 4381)]

private def shiftRow1083 : Array (Nat × Nat) := #[(427, 4382)]

private def shiftRow1084 : Array (Nat × Nat) := #[(372, 4383)]

private def shiftRow1085 : Array (Nat × Nat) := #[(427, 4384)]

private def shiftRow1086 : Array (Nat × Nat) := #[(127, 4385)]

private def shiftRow1087 : Array (Nat × Nat) := #[(280, 4388)]

def shifts016 : Array (Array (Nat × Nat)) := #[
  shiftRow1024,
  shiftRow1025,
  shiftRow1026,
  shiftRow1027,
  shiftRow1028,
  shiftRow1029,
  shiftRow1030,
  shiftRow1031,
  shiftRow1032,
  shiftRow1033,
  shiftRow1034,
  shiftRow1035,
  shiftRow1036,
  shiftRow1037,
  shiftRow1038,
  shiftRow1039,
  shiftRow1040,
  shiftRow1041,
  shiftRow1042,
  shiftRow1043,
  shiftRow1044,
  shiftRow1045,
  shiftRow1046,
  shiftRow1047,
  shiftRow1048,
  shiftRow1049,
  shiftRow1050,
  shiftRow1051,
  shiftRow1052,
  shiftRow1053,
  shiftRow1054,
  shiftRow1055,
  shiftRow1056,
  shiftRow1057,
  shiftRow1058,
  shiftRow1059,
  shiftRow1060,
  shiftRow1061,
  shiftRow1062,
  shiftRow1063,
  shiftRow1064,
  shiftRow1065,
  shiftRow1066,
  shiftRow1067,
  shiftRow1068,
  shiftRow1069,
  shiftRow1070,
  shiftRow1071,
  shiftRow1072,
  shiftRow1073,
  shiftRow1074,
  shiftRow1075,
  shiftRow1076,
  shiftRow1077,
  shiftRow1078,
  shiftRow1079,
  shiftRow1080,
  shiftRow1081,
  shiftRow1082,
  shiftRow1083,
  shiftRow1084,
  shiftRow1085,
  shiftRow1086,
  shiftRow1087
]

end SQLean.PostgresGrammar.Generated
