#!/usr/bin/env python3
"""Writes pentagon-with-orthogonal-square.svg: the minimizer for 9 points on the three-sphere.

    python3 Visualization/make_svg.py

The picture is an animated SVG without scripts. It shows the configuration `X` of `Showcase.lean` in a
stereographic projection of the three-sphere to three-dimensional space. A great circle becomes a circle,
and two orthogonal great circles become two linked circles. The centre of the projection is the point
`P = (cos α, sin α, cos β, sin β) / √2`, which has the same distance from the great circle of the pentagon
and from the great circle of the square. Then the two circles have the radius √2, their centres are the
points `(0, 0, ±1)`, and they lie in two orthogonal planes through the vertical axis. For `α = π/5` and
`β = π/4` a rotation of 180 degrees about this axis maps the picture to itself, so the animation only stores
a turn of 180 degrees and repeats it. Between the stored positions the browser interpolates. The program
uses the standard library of Python only.
"""
import math
import os
import sys

# ---- the configuration ----------------------------------------------------------------------------
X = ([(math.cos(2 * math.pi * k / 5), math.sin(2 * math.pi * k / 5), 0.0, 0.0) for k in range(5)]
     + [(0.0, 0.0, 1.0, 0.0), (0.0, 0.0, -1.0, 0.0), (0.0, 0.0, 0.0, 1.0), (0.0, 0.0, 0.0, -1.0)])
N = len(X)
ENERGY = "35/2"


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


energy = sum(1 / sum((a - b) ** 2 for a, b in zip(X[i], X[j])) for i in range(N) for j in range(i + 1, N))
assert abs(energy - 35 / 2) < 1e-12 and all(abs(dot(p, p) - 1) < 1e-12 for p in X)

# ---- the stereographic projection -----------------------------------------------------------------
ALPHA, BETA = math.pi / 5, math.pi / 4
R2 = math.sqrt(0.5)
POLE = (R2 * math.cos(ALPHA), R2 * math.sin(ALPHA), R2 * math.cos(BETA), R2 * math.sin(BETA))
# an orthonormal basis of the hyperplane orthogonal to the centre of the projection
UP = (R2 * math.cos(ALPHA), R2 * math.sin(ALPHA), -R2 * math.cos(BETA), -R2 * math.sin(BETA))
W1 = (-math.sin(ALPHA), math.cos(ALPHA), 0.0, 0.0)
W2 = (0.0, 0.0, -math.sin(BETA), math.cos(BETA))


def stereo(p):
    """The image of a point of the three-sphere, in the coordinates (W1, W2, UP)."""
    s = 1 - dot(p, POLE)
    return (dot(p, W1) / s, dot(p, W2) / s, dot(p, UP) / s)


IMAGE = [stereo(p) for p in X]
RING = math.sqrt(2)                      # the radius of the two circles
CENTRE = (1.0, -1.0)                     # the heights of their centres
# the circle 0, of the pentagon, lies in the plane of W1 and UP; the circle 1, of the square, in that of W2 and UP
CIRCLE = [0] * 5 + [1] * 4
for i, q in enumerate(IMAGE):
    c = CIRCLE[i]
    assert abs(q[1 - c]) < 1e-12 and abs(math.dist(q, (0, 0, CENTRE[c])) - RING) < 1e-12
AXIS_POINT = [i for i in range(N) if abs(IMAGE[i][0]) < 1e-9 and abs(IMAGE[i][1]) < 1e-9]
assert AXIS_POINT == [3]                 # one vertex of the pentagon lies on the axis

# the rotation of 180 degrees about the axis maps the picture to itself
PARTNER = [min(range(N), key=lambda j: math.dist((-IMAGE[i][0], -IMAGE[i][1], IMAGE[i][2]), IMAGE[j]))
           for i in range(N)]
assert all(math.dist((-IMAGE[i][0], -IMAGE[i][1], IMAGE[i][2]), IMAGE[PARTNER[i]]) < 1e-9 for i in range(N))
assert all(CIRCLE[i] == CIRCLE[PARTNER[i]] for i in range(N))

# A half of a circle is a pair (circle, side): the points of the circle whose coordinate along the horizontal
# direction of its plane has the sign `side`.
HALVES = [(0, 1), (0, -1), (1, 1), (1, -1)]


def half_of(i):
    return CIRCLE[i], (1 if IMAGE[i][CIRCLE[i]] > 0 else -1)


def angle_of(i):
    """The point `i` has the horizontal coordinate `RING sin t` and the height `CENTRE + RING cos t`."""
    c = CIRCLE[i]
    return math.atan2(IMAGE[i][c], IMAGE[i][2] - CENTRE[c])


# ---- the picture ----------------------------------------------------------------------------------
W, HEIGHT = 840, 440
CX, CY = 226, 212                        # the place of the origin in the picture
UNIT = 66.0                              # the length of a unit in the picture
ELEV = math.radians(13)                  # the elevation of the camera
STEPS = 36                               # stored positions per 180 degrees: every 5 degrees
START = math.radians(22.5)               # the rotation of the first picture
BALL = 7.4                               # the radius of a point in the picture
DUR = 24                                 # the time of a turn of 180 degrees, in seconds
KAPPA = 4 / 3 * (math.sqrt(2) - 1)       # the control points of a quarter of a circle

PAGE, INK, INK2, MUTED = "#f9f9f7", "#0b0b0b", "#52514e", "#6f6e69"
BLUE, GREEN = "#2a78d6", "#149a6b"
HAZE = "#e7e8ea"                         # the colour towards which the far side fades
COLOR = (BLUE, GREEN)                    # the pentagon and its circle, the square and its circle
GRAD = ("b", "g")
THETAS = [START + j * math.pi / STEPS for j in range(STEPS + 1)]
BEGIN = ""                               # set by the option --at: the picture at a later time


def horizontal(c, theta):
    """The horizontal unit vector of the plane of the circle `c` after a rotation by `theta`, as the pair
    (to the right, towards the camera)."""
    a = theta + c * math.pi / 2
    return math.cos(a), math.sin(a)


def screen(right, depth, height):
    """The place in the picture of a point; the projection has no perspective."""
    return CX + UNIT * right, CY - UNIT * (height * math.cos(ELEV) - depth * math.sin(ELEV))


def place(c, t, theta):
    """The place of the point of the circle `c` with the angle `t`, and its depth in units of the radius."""
    hx, hd = horizontal(c, theta)
    s = RING * math.sin(t)
    return (*screen(s * hx, s * hd, CENTRE[c] + RING * math.cos(t)), math.sin(t) * hd)


def depth_of(h, theta):
    """The depth of the middle of a half, in units of the radius: positive on the side of the camera."""
    c, side = HALVES[h]
    return side * horizontal(c, theta)[1]


def slot_of(h, theta):
    """The layer of a half. The circle that is seen more from the side is the outer one: its far half is drawn
    first (0) and its near half last (2). The two halves of the other circle are drawn in between (1). At a
    crossing of the two circles the order is then the order of the depths."""
    d = depth_of(h, theta)
    return 1 if abs(d) < R2 else (0 if d < 0 else 2)


# the layers change at the rotations 45, 135, ... degrees, in the middle between two stored positions; at these
# rotations the two halves that change their order do not meet in the picture
EVENTS = [k for k in range(1, 2 * STEPS) if abs(math.cos(2 * (START + k * math.pi / (2 * STEPS)))) < 1e-9]
assert EVENTS and all(k % 2 == 1 for k in EVENTS)


def num(x, digits=1):
    s = f"{x:.{digits}f}"
    if "." in s:
        s = s.rstrip("0").rstrip(".")
    return "0" if s in ("-0", "") else s


def mix(color, other, t):
    a = [int(color[i:i + 2], 16) for i in (1, 3, 5)]
    b = [int(other[i:i + 2], 16) for i in (1, 3, 5)]
    return "#" + "".join(f"{round(x + (y - x) * t):02x}" for x, y in zip(a, b))


def animation(tag, attr, values, extra=""):
    return (f'<{tag} attributeName="{attr}"{extra} dur="{DUR}s"{BEGIN} repeatCount="indefinite" '
            f'values="{";".join(values)}"/>')


def switched(inner, shown):
    """A group that is visible while `shown(theta)` holds; this changes only at the rotations of EVENTS."""
    states = [shown(START + (k + 1) * math.pi / (2 * STEPS)) for k in [-1] + EVENTS]
    if not any(states):
        return ""
    if all(states):
        return f"<g>{inner}</g>"
    times = ["0"] + [num(k / (2 * STEPS), 4) for k in EVENTS]
    values = ["1" if s else "0" for s in states]
    return (f'<g opacity="{values[0]}">'
            + animation("animate", "opacity", values, f' calcMode="discrete" keyTimes="{";".join(times)}"')
            + inner + "</g>")


def half_path(h):
    """A half of a circle as two cubic curves, from its top to its bottom. The picture of a circle under a
    projection without perspective is an affine image, and so are the control points of the curves. The colour
    fades with the depth of the half."""
    c, side = HALVES[h]
    ctrl = [(0, 1), (KAPPA, 1), (1, KAPPA), (1, 0), (1, -KAPPA), (KAPPA, -1), (0, -1)]
    ds, colors = [], []
    for th in THETAS:
        hx, hd = horizontal(c, th)
        p = [screen(side * RING * u * hx, side * RING * u * hd, CENTRE[c] + RING * v) for u, v in ctrl]
        f = [f"{num(x)} {num(y)}" for x, y in p]
        ds.append(f"M{f[0]}C{f[1]} {f[2]} {f[3]}C{f[4]} {f[5]} {f[6]}")
        colors.append(mix(COLOR[c], HAZE, 0.62 * (1 - depth_of(h, th)) / 2))
    return (f'<path d="{ds[0]}" stroke="{colors[0]}">' + animation("animate", "d", ds)
            + animation("animate", "stroke", colors) + "</path>")


def point(i):
    """A point: a pale copy, and over it a copy in full colour that fades with the depth."""
    c = CIRCLE[i]
    t = angle_of(i)
    xs = [place(c, t, th) for th in THETAS]
    pos = [f"{num(x)} {num(y)}" for x, y, _ in xs]
    rad = [num(BALL * (1 + 0.09 * d), 2) for _, _, d in xs]
    near = [num(min(1.0, max(0.0, 0.5 + 0.62 * d)), 2) for _, _, d in xs]
    r = animation("animate", "r", rad)
    return (f'<g transform="translate({pos[0]})">'
            + animation("animateTransform", "transform", pos, ' type="translate"')
            + f'<circle r="{rad[0]}" fill="url(#{GRAD[c]}f)">{r}</circle>'
            + f'<circle r="{rad[0]}" fill="url(#{GRAD[c]})" opacity="{near[0]}">{r}'
            + animation("animate", "opacity", near) + "</circle></g>")


def axis_point():
    """The vertex of the pentagon on the axis does not move, and its depth is zero."""
    x, y = screen(0.0, 0.0, IMAGE[AXIS_POINT[0]][2])
    at = f'cx="{num(x)}" cy="{num(y)}" r="{num(BALL, 2)}"'
    return f'<circle {at} fill="url(#bf)"/><circle {at} fill="url(#b)" opacity=".5"/>'


def body():
    """The moving part of the picture, from the farthest layer to the nearest."""
    halves = [half_path(h) + "".join(point(i) for i in range(N) if i not in AXIS_POINT and half_of(i) == HALVES[h])
              for h in range(4)]
    parts = []
    for slot in range(3):
        for h in range(4):
            parts.append(switched(halves[h], lambda th, h=h, slot=slot: slot_of(h, th) == slot))
        if slot == 1:
            # while the circle of the pentagon is the inner one, the other circle may pass in front of this vertex
            parts.append(switched(axis_point(), lambda th: slot_of(0, th) == 1))
    parts.append(switched(axis_point(), lambda th: slot_of(0, th) != 1))
    return [p for p in parts if p]


def gradient(name, color, haze=0.0):
    stops = [(0, mix(color, "#ffffff", 0.62)), (.45, color), (1, mix(color, "#000000", 0.38))]
    return (f'<radialGradient id="{name}" cx=".34" cy=".3" r=".8">'
            + "".join(f'<stop offset="{num(o, 2)}" stop-color="{mix(c, HAZE, haze)}"/>' for o, c in stops)
            + "</radialGradient>")


TX = 462                                 # the left edge of the text


def legend(y, c, text):
    return (f'<circle cx="{TX + 6}" cy="{y - 5}" r="5.5" fill="url(#{GRAD[c]})"/>'
            f'<text x="{TX + 23}" y="{y}">{text}</text>')


def check_loop():
    """After 180 degrees the picture is the first picture: every half and every point stands where its
    partner stood."""
    first, last = THETAS[0], THETAS[-1]
    for h, (c, side) in enumerate(HALVES):
        g = HALVES.index((c, -side))
        assert abs(depth_of(h, last) - depth_of(g, first)) < 1e-9 and slot_of(h, last) == slot_of(g, first)
        assert all(abs(u - v) < 1e-9 for t in (0.3, 1.2, 2.5)
                   for u, v in zip(place(c, side * t, last), place(c, -side * t, first)))
    for i in range(N):
        if i not in AXIS_POINT:
            j = PARTNER[i]
            assert half_of(j) == (CIRCLE[i], -half_of(i)[1])
            assert all(abs(u - v) < 1e-9 for u, v in zip(place(CIRCLE[i], angle_of(i), last),
                                                         place(CIRCLE[j], angle_of(j), first)))


def svg():
    font = "Inter,system-ui,-apple-system,'Segoe UI',Helvetica,Arial,sans-serif"
    ground = screen(0.0, 0.0, -1 - RING)[1] + 22
    parts = [
        f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {HEIGHT}" width="{W}" height="{HEIGHT}" '
        f'font-family="{font}" role="img" aria-labelledby="t d">',
        '<title id="t">The minimizer for 9 points on the three-sphere: a pentagon with an orthogonal square</title>',
        '<desc id="d">Nine points on the unit sphere of four-dimensional space, in a stereographic projection: '
        'a regular pentagon on a great circle and a square on the orthogonal great circle. The two great circles '
        f'appear as two linked circles, which rotate about their common axis. The harmonic energy {ENERGY} of '
        'this configuration is the minimum for 9 points.</desc>',
        "<defs>",
        gradient("b", BLUE), gradient("g", GREEN), gradient("bf", BLUE, 0.5), gradient("gf", GREEN, 0.5),
        '<radialGradient id="shadow"><stop offset="0" stop-color="#141a2a" stop-opacity=".17"/>'
        '<stop offset=".6" stop-color="#141a2a" stop-opacity=".05"/>'
        '<stop offset="1" stop-color="#141a2a" stop-opacity="0"/></radialGradient>',
        "</defs>",
        f'<rect x=".5" y=".5" width="{W - 1}" height="{HEIGHT - 1}" rx="14" fill="{PAGE}" stroke="{INK}" '
        'stroke-opacity=".1"/>',
        f'<ellipse cx="{CX}" cy="{num(ground)}" rx="{round(UNIT * 1.2)}" ry="11" fill="url(#shadow)"/>',
        '<g fill="none" stroke-width="3.2" stroke-linecap="round">',
        *body(), "</g>",
        # the text, in the manner of the page lukasliehr.github.io/energy-minimization
        f'<text x="{TX}" y="82" font-size="13" fill="{MUTED}">Harmonic energy of 9 points on S³</text>',
        f'<text font-size="23" font-weight="600" fill="{INK}" letter-spacing="-.35">'
        f'<tspan x="{TX}" y="114">Regular pentagon</tspan>'
        f'<tspan x="{TX}" y="142">with orthogonal square</tspan></text>',
        f'<g font-size="14" fill="{INK2}">',
        legend(186, 0, "Five points: a pentagon on a great circle"),
        legend(214, 1, "Four points: a square on the orthogonal circle"),
        "</g>",
        f'<text font-size="12.5" fill="{MUTED}"><tspan x="{TX}" y="246">Stereographic projection of S³, in which the two</tspan>'
        f'<tspan x="{TX}" y="264">great circles appear as linked circles</tspan></text>',
        f'<line x1="{TX}" y1="290" x2="{W - 44}" y2="290" stroke="{INK}" stroke-opacity=".1"/>',
        f'<text x="{TX}" y="320" font-size="12" fill="{MUTED}">Minimal harmonic energy</text>',
        f'<text x="{TX}" y="354" font-size="27" font-weight="600" fill="{INK}" letter-spacing="-.5">{ENERGY}</text>',
        "</svg>",
    ]
    return "\n".join(parts) + "\n"


if __name__ == "__main__":
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "pentagon-with-orthogonal-square.svg")
    if len(sys.argv) == 4 and sys.argv[1] == "--at":
        # for a look at a later moment of the animation: python3 make_svg.py --at SECONDS FILE
        BEGIN, path = f' begin="-{sys.argv[2]}s"', sys.argv[3]
    check_loop()
    text = svg()
    with open(path, "w", encoding="utf-8") as f:
        f.write(text)
    print(path, len(text.encode()), "bytes")
