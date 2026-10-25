import hashlib
import os
import time
import gradio as gr

def multiplicar_en_campo(a, b):
    res = 0
    for _ in range(8):
        if b & 1:
            res ^= a
        carry = a & 0x80
        a = (a << 1) & 0xFF
        if carry:
            a ^= 0x1B
        b >>= 1
    return res

def division_polinomios(a, b):
    q, r = 0, a
    grado_b = b.bit_length() - 1
    while r.bit_length() - 1 >= grado_b and r != 0:
        d = (r.bit_length() - 1) - grado_b
        q ^= 1 << d
        r ^= b << d
    return q, r

def multiplicar_polinomios(a, b):
    res = 0
    while b:
        if b & 1:
            res ^= a
        a <<= 1
        b >>= 1
    return res

def inverso_en_campo(a):
    if a == 0:
        return 0
    r0, r1 = 0x11B, a
    s0, s1 = 0, 1
    while r1 != 0:
        q, r = division_polinomios(r0, r1)
        r0, r1 = r1, r
        s0, s1 = s1, s0 ^ multiplicar_polinomios(q, s1)
    return s0

def rotar_bits_izquierda(b, n):
    return ((b << n) | (b >> (8 - n))) & 0xFF

def construir_sbox():
    sbox = [0] * 256
    for b in range(256):
        inv = inverso_en_campo(b)
        sbox[b] = (inv ^ rotar_bits_izquierda(inv, 1) ^ rotar_bits_izquierda(inv, 2)
                   ^ rotar_bits_izquierda(inv, 3) ^ rotar_bits_izquierda(inv, 4) ^ 0x63)
    return sbox

def construir_sbox_inversa(sbox):
    inv = [0] * 256
    for i, v in enumerate(sbox):
        inv[v] = i
    return inv

SBOX = construir_sbox()
SBOX_INV = construir_sbox_inversa(SBOX)

def sub_bytes(estado):
    return [[SBOX[estado[f][c]] for c in range(4)] for f in range(4)]

def inv_sub_bytes(estado):
    return [[SBOX_INV[estado[f][c]] for c in range(4)] for f in range(4)]

def shift_rows(estado):
    return [[estado[f][(c + f) % 4] for c in range(4)] for f in range(4)]

def inv_shift_rows(estado):
    return [[estado[f][(c - f) % 4] for c in range(4)] for f in range(4)]

def mix_columns(estado):
    nuevo = [[0]*4 for _ in range(4)]
    for c in range(4):
        a = [estado[f][c] for f in range(4)]
        nuevo[0][c] = multiplicar_en_campo(a[0], 2) ^ multiplicar_en_campo(a[1], 3) ^ a[2] ^ a[3]
        nuevo[1][c] = a[0] ^ multiplicar_en_campo(a[1], 2) ^ multiplicar_en_campo(a[2], 3) ^ a[3]
        nuevo[2][c] = a[0] ^ a[1] ^ multiplicar_en_campo(a[2], 2) ^ multiplicar_en_campo(a[3], 3)
        nuevo[3][c] = multiplicar_en_campo(a[0], 3) ^ a[1] ^ a[2] ^ multiplicar_en_campo(a[3], 2)
    return nuevo

def inv_mix_columns(estado):
    nuevo = [[0]*4 for _ in range(4)]
    for c in range(4):
        a = [estado[f][c] for f in range(4)]
        nuevo[0][c] = (multiplicar_en_campo(a[0], 14) ^ multiplicar_en_campo(a[1], 11)
                       ^ multiplicar_en_campo(a[2], 13) ^ multiplicar_en_campo(a[3], 9))
        nuevo[1][c] = (multiplicar_en_campo(a[0], 9) ^ multiplicar_en_campo(a[1], 14)
                       ^ multiplicar_en_campo(a[2], 11) ^ multiplicar_en_campo(a[3], 13))
        nuevo[2][c] = (multiplicar_en_campo(a[0], 13) ^ multiplicar_en_campo(a[1], 9)
                       ^ multiplicar_en_campo(a[2], 14) ^ multiplicar_en_campo(a[3], 11))
        nuevo[3][c] = (multiplicar_en_campo(a[0], 11) ^ multiplicar_en_campo(a[1], 13)
                       ^ multiplicar_en_campo(a[2], 9) ^ multiplicar_en_campo(a[3], 14))
    return nuevo

def add_round_key(estado, clave_ronda):
    return [[estado[f][c] ^ clave_ronda[f][c] for c in range(4)] for f in range(4)]

def expandir_clave(clave, nk):
    nr = {4: 10, 6: 12, 8: 14}[nk]
    palabras = [list(clave[i:i+4]) for i in range(0, len(clave), 4)]
    rcon = [0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1B, 0x36]
    total = 4 * (nr + 1)
    for i in range(nk, total):
        temp = palabras[i-1].copy()
        if i % nk == 0:
            temp = temp[1:] + temp[:1]
            temp = [SBOX[b] for b in temp]
            temp[0] ^= rcon[i//nk - 1]
        elif nk > 6 and i % nk == 4:
            temp = [SBOX[b] for b in temp]
        palabras.append([palabras[i-nk][j] ^ temp[j] for j in range(4)])
    return [palabras[4*i:4*i+4] for i in range(nr + 1)], nr

def clave_a_estado(clave):
    return [[clave[f + 4*c] for c in range(4)] for f in range(4)]

def estado_a_matriz(palabras):
    return [[palabras[c][f] for c in range(4)] for f in range(4)]

def matriz_a_bytes(estado):
    return bytes([estado[f][c] for c in range(4) for f in range(4)])

def rellenar(datos, bloque=16):
    falta = bloque - (len(datos) % bloque)
    return datos + bytes([falta] * falta)

def verificar_relleno(datos):
    if not datos:
        return False
    ultimo = datos[-1]
    if ultimo < 1 or ultimo > 16:
        return False
    if len(datos) < ultimo:
        return False
    return all(b == ultimo for b in datos[-ultimo:])

def quitar_relleno(datos):
    return datos[:-datos[-1]]

def cifrar_bloque(bloque, subclaves, nr):
    estado = clave_a_estado(bloque)
    estado = add_round_key(estado, estado_a_matriz(subclaves[0]))
    for ronda in range(1, nr):
        estado = sub_bytes(estado)
        estado = shift_rows(estado)
        estado = mix_columns(estado)
        estado = add_round_key(estado, estado_a_matriz(subclaves[ronda]))
    estado = sub_bytes(estado)
    estado = shift_rows(estado)
    estado = add_round_key(estado, estado_a_matriz(subclaves[nr]))
    return matriz_a_bytes(estado)

def descifrar_bloque(bloque, subclaves, nr):
    estado = clave_a_estado(bloque)
    estado = add_round_key(estado, estado_a_matriz(subclaves[nr]))
    for ronda in range(nr - 1, 0, -1):
        estado = inv_shift_rows(estado)
        estado = inv_sub_bytes(estado)
        estado = add_round_key(estado, estado_a_matriz(subclaves[ronda]))
        estado = inv_mix_columns(estado)
    estado = inv_shift_rows(estado)
    estado = inv_sub_bytes(estado)
    estado = add_round_key(estado, estado_a_matriz(subclaves[0]))
    return matriz_a_bytes(estado)

def cifrar(mensaje, clave, nk):
    subclaves, nr = expandir_clave(clave, nk)
    datos = rellenar(mensaje)
    return b"".join(cifrar_bloque(datos[i:i+16], subclaves, nr)
                    for i in range(0, len(datos), 16))

def descifrar(cifrado, clave, nk):
    subclaves, nr = expandir_clave(clave, nk)
    datos = b"".join(descifrar_bloque(cifrado[i:i+16], subclaves, nr)
                     for i in range(0, len(cifrado), 16))
    if not verificar_relleno(datos):
        raise ValueError("La contraseña es incorrecta o el mensaje fue alterado.")
    return quitar_relleno(datos)

# --- SALAS DE CHAT (cada contraseña es una sala independiente) ---
historial_salas = {}

def obtener_historial(contrasena):
    return historial_salas.setdefault(contrasena, [])

def formatear_historial(contrasena, variante="AES-128"):
    if not contrasena:
        return "Escribe una contraseña para ver los mensajes de la sala."
    
    historial = obtener_historial(contrasena)
    if not historial:
        return "No hay mensajes aún en esta sala."
    
    nk = {"AES-128": 4, "AES-192": 6, "AES-256": 8}[variante]
    clave = hashlib.sha256(contrasena.encode()).digest()[:nk*4]
    lineas = []
    
    for msg in historial:
        lineas.append(f"[{msg['hora']}] {msg['nombre']}:")
        lineas.append(f"  Cifrado (hex): {msg['cifrado']}")
        try:
            cifrado_bytes = bytes.fromhex(msg['cifrado'])
            descifrado = descifrar(cifrado_bytes, clave, nk)
            lineas.append(f"  Descifrado: {descifrado.decode('utf-8', errors='replace')}")
        except Exception:
            pass
        lineas.append("")
    
    return "\n".join(lineas)

def enviar_mensaje(nombre, mensaje, contrasena, variante):
    if not nombre or not mensaje or not contrasena:
        return "Escribe tu nombre, un mensaje y la contraseña.", formatear_historial(contrasena, variante)

    nk = {"AES-128": 4, "AES-192": 6, "AES-256": 8}[variante]
    clave = hashlib.sha256(contrasena.encode()).digest()[:nk*4]
    
    cifrado = cifrar(mensaje.encode(), clave, nk)
    hex_cifrado = cifrado.hex().upper()
    
    obtener_historial(contrasena).append({
        "nombre": nombre,
        "cifrado": hex_cifrado,
        "hora": time.strftime("%H:%M:%S")
    })
    
    return "Mensaje enviado.", formatear_historial(contrasena, variante)

def actualizar_chat(contrasena, variante):
    return formatear_historial(contrasena, variante)

with gr.Blocks(title="Chat AES") as demo:
    gr.Markdown("# Chat Cifrado con AES\nCada contraseña crea una sala independiente. Solo quienes tengan la misma contraseña verán el texto claro; los demás solo verán el hexadecimal.")

    with gr.Row():
        with gr.Column(scale=1):
            nombre = gr.Textbox(label="Tu nombre")
            contrasena = gr.Textbox(label="Contraseña de la sala", type="password")
            variante = gr.Radio(["AES-128", "AES-192", "AES-256"], value="AES-128", label="Variante")
            
            gr.Markdown("---")
            gr.Markdown("### Enviar mensaje")
            mensaje = gr.Textbox(label="Mensaje", lines=3)
            boton_enviar = gr.Button("Enviar mensaje cifrado", variant="primary")
            estado = gr.Textbox(label="Estado", interactive=False)

        with gr.Column(scale=2):
            gr.Markdown("### Historial de la sala")
            chat = gr.Textbox(label="Mensajes", lines=25, interactive=False)
            boton_actualizar = gr.Button("Actualizar chat")

    boton_enviar.click(
        enviar_mensaje,
        [nombre, mensaje, contrasena, variante],
        [estado, chat]
    )
    
    boton_actualizar.click(
        actualizar_chat,
        [contrasena, variante],
        [chat]
    )

demo.launch(server_name="0.0.0.0", server_port=int(os.environ.get("PORT", 7860)))
