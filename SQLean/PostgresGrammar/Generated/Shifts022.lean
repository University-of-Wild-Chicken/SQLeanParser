import SQLean.PostgresGrammar.Syntax

/-! Generated from PostgreSQL 16.15 at f0595c3d839debdb140903621c1b44a4f4d86256.
Regenerate with scripts/generate_postgresql_grammar.py; no upstream C actions execute. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
namespace SQLean.PostgresGrammar.Generated

private def shiftRow1408 : Array (Nat × Nat) := #[(424, 5196)]

private def shiftRow1409 : Array (Nat × Nat) := #[(290, 5197)]

private def shiftRow1410 : Array (Nat × Nat) := #[(309, 5200), (378, 40), (415, 44), (457, 48), (470, 49), (494, 50), (513, 56)]

private def shiftRow1411 : Array (Nat × Nat) := #[(295, 5203), (513, 5204)]

private def shiftRow1412 : Array (Nat × Nat) := #[(503, 5207)]

private def shiftRow1413 : Array (Nat × Nat) := #[(437, 5210)]

private def shiftRow1414 : Array (Nat × Nat) := #[(514, 5211), (517, 3474)]

private def shiftRow1415 : Array (Nat × Nat) := #[(427, 5212)]

private def shiftRow1416 : Array (Nat × Nat) := #[(174, 5214)]

private def shiftRow1417 : Array (Nat × Nat) := #[(514, 5217), (517, 5218)]

private def shiftRow1418 : Array (Nat × Nat) := #[(470, 5219)]

private def shiftRow1419 : Array (Nat × Nat) := #[(78, 5220)]

private def shiftRow1420 : Array (Nat × Nat) := #[(78, 5220), (511, 1017), (515, 1018)]

private def shiftRow1421 : Array (Nat × Nat) := #[(514, 5224), (517, 3129)]

private def shiftRow1422 : Array (Nat × Nat) := #[(514, 5225), (517, 3129)]

private def shiftRow1423 : Array (Nat × Nat) := #[(514, 5226), (517, 3129)]

private def shiftRow1424 : Array (Nat × Nat) := #[(122, 5227), (194, 5228)]

private def shiftRow1425 : Array (Nat × Nat) := #[(205, 5229)]

private def shiftRow1426 : Array (Nat × Nat) := #[(121, 5230), (453, 5231)]

private def shiftRow1427 : Array (Nat × Nat) := #[(3, 635), (20, 235), (21, 236), (22, 237), (23, 238), (24, 239), (25, 240), (26, 241), (27, 242), (28, 243), (30, 244), (31, 245), (32, 246), (40, 247), (41, 248), (42, 249), (44, 250), (45, 251), (46, 252), (47, 253), (49, 255), (50, 256), (51, 257), (52, 258), (53, 259), (55, 261), (56, 262), (58, 263), (59, 264), (60, 265), (61, 266), (62, 267), (63, 268), (64, 269), (67, 270), (68, 271), (69, 272), (70, 273), (71, 274), (73, 275), (74, 276), (75, 277), (76, 278), (77, 279), (81, 281), (82, 282), (83, 283), (84, 284), (85, 285), (86, 286), (88, 288), (89, 289), (90, 290), (92, 291), (93, 292), (94, 293), (95, 294), (96, 295), (97, 296), (100, 298), (101, 299), (102, 300), (110, 302), (111, 303), (112, 304), (113, 305), (114, 306), (115, 307), (116, 308), (117, 309), (118, 310), (119, 5244), (120, 311), (122, 312), (123, 313), (124, 314), (125, 315), (126, 316), (127, 317), (128, 318), (130, 319), (131, 320), (132, 321), (133, 322), (136, 323), (137, 324), (138, 325), (139, 326), (140, 327), (142, 328), (143, 329), (144, 330), (146, 331), (147, 332), (148, 333), (150, 334), (151, 335), (152, 336), (153, 337), (154, 338), (155, 339), (156, 340), (157, 341), (158, 342), (159, 343), (161, 344), (163, 345), (164, 346), (165, 347), (166, 348), (167, 349), (169, 350), (171, 351), (172, 352), (176, 355), (177, 356), (178, 357), (179, 358), (181, 359), (182, 360), (184, 361), (185, 362), (186, 363), (188, 364), (189, 365), (190, 366), (191, 367), (192, 368), (194, 370), (195, 371), (196, 372), (197, 373), (199, 374), (200, 375), (201, 376), (202, 377), (203, 378), (204, 379), (205, 380), (206, 381), (208, 382), (210, 384), (211, 385), (212, 386), (213, 387), (214, 388), (215, 389), (216, 390), (218, 391), (220, 392), (223, 395), (225, 397), (226, 398), (227, 399), (228, 400), (229, 401), (230, 402), (231, 403), (232, 404), (233, 405), (234, 406), (235, 407), (238, 408), (239, 409), (241, 411), (244, 413), (245, 414), (246, 415), (249, 416), (250, 417), (251, 418), (252, 419), (253, 420), (254, 421), (255, 422), (256, 423), (257, 424), (258, 425), (259, 426), (260, 427), (261, 428), (262, 429), (263, 430), (264, 431), (265, 432), (266, 433), (267, 434), (269, 436), (270, 437), (271, 438), (272, 439), (273, 440), (274, 441), (275, 442), (276, 443), (277, 444), (278, 445), (279, 446), (281, 447), (282, 448), (284, 450), (286, 451), (287, 452), (288, 453), (289, 454), (290, 455), (291, 456), (293, 457), (294, 458), (297, 459), (298, 460), (299, 461), (302, 462), (303, 463), (304, 464), (306, 466), (308, 468), (309, 469), (310, 470), (311, 471), (312, 472), (313, 473), (314, 474), (315, 475), (316, 476), (317, 477), (318, 478), (320, 479), (321, 480), (322, 481), (323, 482), (324, 483), (325, 484), (326, 485), (327, 486), (329, 487), (330, 488), (331, 489), (332, 490), (333, 491), (334, 492), (335, 493), (336, 494), (337, 495), (338, 496), (339, 497), (340, 498), (341, 499), (342, 500), (343, 501), (345, 502), (346, 503), (347, 504), (348, 505), (349, 506), (350, 507), (351, 508), (352, 509), (353, 510), (354, 511), (355, 512), (356, 513), (357, 514), (359, 515), (360, 516), (362, 518), (363, 519), (364, 520), (365, 521), (366, 522), (367, 523), (368, 524), (369, 525), (370, 526), (371, 527), (372, 528), (373, 529), (374, 530), (375, 531), (376, 532), (377, 533), (379, 534), (380, 535), (381, 536), (382, 537), (383, 538), (385, 539), (386, 540), (387, 541), (388, 542), (389, 543), (391, 545), (392, 546), (393, 547), (394, 548), (396, 549), (397, 550), (398, 551), (399, 552), (400, 553), (401, 554), (402, 555), (403, 556), (404, 557), (405, 558), (406, 559), (407, 560), (408, 561), (409, 562), (410, 563), (412, 564), (413, 565), (416, 566), (418, 568), (419, 569), (420, 570), (421, 571), (422, 572), (424, 573), (425, 574), (426, 575), (429, 576), (430, 577), (431, 578), (432, 579), (433, 580), (435, 581), (436, 582), (437, 583), (438, 584), (439, 585), (440, 586), (441, 587), (442, 588), (445, 589), (446, 590), (447, 591), (448, 592), (449, 593), (452, 594), (453, 595), (454, 596), (455, 597), (456, 598), (457, 599), (458, 600), (460, 601), (462, 603), (463, 604), (464, 605), (465, 606), (468, 607), (471, 608), (472, 609), (473, 610), (474, 611), (475, 612), (476, 613), (477, 614), (478, 615), (479, 616), (480, 617), (481, 618), (482, 619), (483, 620), (484, 621), (485, 622), (486, 623), (487, 624), (488, 625), (489, 626), (490, 627)]

private def shiftRow1428 : Array (Nat × Nat) := #[(192, 5249)]

private def shiftRow1429 : Array (Nat × Nat) := #[(192, 5250)]

private def shiftRow1430 : Array (Nat × Nat) := #[(285, 5251)]

private def shiftRow1431 : Array (Nat × Nat) := #[(285, 5254)]

private def shiftRow1432 : Array (Nat × Nat) := #[(38, 1613), (60, 1614), (111, 1615), (178, 4831), (201, 1616), (252, 1617), (257, 1618), (261, 1619), (276, 2885), (310, 1621), (355, 1623), (379, 1624), (399, 1626), (447, 1627)]

private def shiftRow1433 : Array (Nat × Nat) := #[(503, 5259)]

private def shiftRow1434 : Array (Nat × Nat) := #[(59, 5260)]

private def shiftRow1435 : Array (Nat × Nat) := #[(418, 5261)]

private def shiftRow1436 : Array (Nat × Nat) := #[(517, 5273)]

private def shiftRow1437 : Array (Nat × Nat) := #[(517, 5276)]

private def shiftRow1438 : Array (Nat × Nat) := #[(427, 5280)]

private def shiftRow1439 : Array (Nat × Nat) := #[(72, 5282)]

private def shiftRow1440 : Array (Nat × Nat) := #[(427, 5286)]

private def shiftRow1441 : Array (Nat × Nat) := #[(427, 5287)]

private def shiftRow1442 : Array (Nat × Nat) := #[(174, 5288), (198, 5289), (470, 5290)]

private def shiftRow1443 : Array (Nat × Nat) := #[(154, 5295)]

private def shiftRow1444 : Array (Nat × Nat) := #[(157, 5296)]

private def shiftRow1445 : Array (Nat × Nat) := #[(427, 5303)]

private def shiftRow1446 : Array (Nat × Nat) := #[(514, 5304)]

private def shiftRow1447 : Array (Nat × Nat) := #[(221, 5305)]

private def shiftRow1448 : Array (Nat × Nat) := #[(513, 5310)]

private def shiftRow1449 : Array (Nat × Nat) := #[(126, 5314)]

private def shiftRow1450 : Array (Nat × Nat) := #[(176, 5315), (210, 5316)]

private def shiftRow1451 : Array (Nat × Nat) := #[(176, 5317)]

private def shiftRow1452 : Array (Nat × Nat) := #[(72, 4438), (119, 4441), (178, 4443), (280, 5319), (285, 4446), (328, 4447), (344, 4448), (444, 4449)]

private def shiftRow1453 : Array (Nat × Nat) := #[(119, 5321)]

private def shiftRow1454 : Array (Nat × Nat) := #[(38, 5322)]

private def shiftRow1455 : Array (Nat × Nat) := #[(35, 5327), (153, 5328)]

private def shiftRow1456 : Array (Nat × Nat) := #[(198, 5329)]

private def shiftRow1457 : Array (Nat × Nat) := #[(290, 5332)]

private def shiftRow1458 : Array (Nat × Nat) := #[(151, 5335), (200, 5336)]

private def shiftRow1459 : Array (Nat × Nat) := #[(513, 5337)]

private def shiftRow1460 : Array (Nat × Nat) := #[(382, 5338)]

private def shiftRow1461 : Array (Nat × Nat) := #[(451, 5339)]

private def shiftRow1462 : Array (Nat × Nat) := #[(38, 5341)]

private def shiftRow1463 : Array (Nat × Nat) := #[(280, 5345)]

private def shiftRow1464 : Array (Nat × Nat) := #[(290, 3051), (316, 3052), (513, 5346)]

private def shiftRow1465 : Array (Nat × Nat) := #[(170, 5347)]

private def shiftRow1466 : Array (Nat × Nat) := #[(382, 5351)]

private def shiftRow1467 : Array (Nat × Nat) := #[(153, 5353), (378, 40), (415, 44), (457, 48), (470, 49), (494, 50), (513, 56)]

private def shiftRow1468 : Array (Nat × Nat) := #[(290, 5356)]

private def shiftRow1469 : Array (Nat × Nat) := #[(514, 5359), (517, 5360)]

private def shiftRow1470 : Array (Nat × Nat) := #[(470, 5361)]

private def shiftRow1471 : Array (Nat × Nat) := #[(59, 5363)]

def shifts022 : Array (Array (Nat × Nat)) := #[
  shiftRow1408,
  shiftRow1409,
  shiftRow1410,
  shiftRow1411,
  shiftRow1412,
  shiftRow1413,
  shiftRow1414,
  shiftRow1415,
  shiftRow1416,
  shiftRow1417,
  shiftRow1418,
  shiftRow1419,
  shiftRow1420,
  shiftRow1421,
  shiftRow1422,
  shiftRow1423,
  shiftRow1424,
  shiftRow1425,
  shiftRow1426,
  shiftRow1427,
  shiftRow1428,
  shiftRow1429,
  shiftRow1430,
  shiftRow1431,
  shiftRow1432,
  shiftRow1433,
  shiftRow1434,
  shiftRow1435,
  shiftRow1436,
  shiftRow1437,
  shiftRow1438,
  shiftRow1439,
  shiftRow1440,
  shiftRow1441,
  shiftRow1442,
  shiftRow1443,
  shiftRow1444,
  shiftRow1445,
  shiftRow1446,
  shiftRow1447,
  shiftRow1448,
  shiftRow1449,
  shiftRow1450,
  shiftRow1451,
  shiftRow1452,
  shiftRow1453,
  shiftRow1454,
  shiftRow1455,
  shiftRow1456,
  shiftRow1457,
  shiftRow1458,
  shiftRow1459,
  shiftRow1460,
  shiftRow1461,
  shiftRow1462,
  shiftRow1463,
  shiftRow1464,
  shiftRow1465,
  shiftRow1466,
  shiftRow1467,
  shiftRow1468,
  shiftRow1469,
  shiftRow1470,
  shiftRow1471
]

end SQLean.PostgresGrammar.Generated
