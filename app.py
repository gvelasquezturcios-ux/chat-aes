
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

# --- ESTADO GLOBAL ---
CLAVE_GENERAL = "general"
historial_general = []
usuarios_general = set()
salas_privadas = {}

def formatear_general():
    if not historial_general:
        return []
    clave_aes = hashlib.sha256(CLAVE_GENERAL.encode()).digest()[:32]
    mensajes = []
    for msg in historial_general:
        try:
            cifrado_bytes = bytes.fromhex(msg['cifrado'])
            descifrado = descifrar(cifrado_bytes, clave_aes, 8)
            texto = descifrado.decode('utf-8', errors='replace')
        except Exception:
            texto = msg['cifrado']
        mensajes.append({"role": "user", "content": f"**{msg['nombre']}**: {texto}"})
    return mensajes

def formatear_privada(nombre_sala, clave_ingresada):
    if nombre_sala not in salas_privadas:
        return []
    sala = salas_privadas[nombre_sala]
    if not sala["mensajes"]:
        return []
    
    clave_correcta = (clave_ingresada == sala["clave"])
    clave_aes = hashlib.sha256(sala["clave"].encode()).digest()[:32] if clave_correcta else None
    
    mensajes = []
    for msg in sala["mensajes"]:
        if clave_correcta:
            try:
                cifrado_bytes = bytes.fromhex(msg['cifrado'])
                descifrado = descifrar(cifrado_bytes, clave_aes, 8)
                texto = descifrado.decode('utf-8', errors='replace')
            except Exception:
                texto = msg['cifrado']
        else:
            texto = msg['cifrado']
        mensajes.append({"role": "user", "content": f"**{msg['nombre']}**: {texto}"})
    return mensajes

def entrar_general(nombre):
    if not nombre:
        return gr.update(visible=True), gr.update(visible=False), "⚠️ Escribe tu nombre."
    return gr.update(visible=False), gr.update(visible=True), f"✅ Bienvenido, {nombre}."

def enviar_general(nombre_guardado, mensaje):
    if not nombre_guardado or not mensaje:
        return "", formatear_general()
    if nombre_guardado in usuarios_general:
        return f"⚠️ El nombre '{nombre_guardado}' ya está en uso.", formatear_general()
    
    clave_aes = hashlib.sha256(CLAVE_GENERAL.encode()).digest()[:32]
    cifrado = cifrar(mensaje.encode(), clave_aes, 8)
    historial_general.append({
        "nombre": nombre_guardado,
        "cifrado": cifrado.hex().upper(),
        "hora": time.strftime("%H:%M")
    })
    usuarios_general.add(nombre_guardado)
    return "", formatear_general()

def crear_privada(nombre_sala, clave_sala):
    if not nombre_sala or not clave_sala:
        return "⚠️ Escribe un nombre y una clave para la sala."
    if nombre_sala in salas_privadas:
        return f"⚠️ La sala '{nombre_sala}' ya existe."
    salas_privadas[nombre_sala] = {"clave": clave_sala, "mensajes": [], "usuarios": set()}
    return f"✅ Sala '{nombre_sala}' creada."

def entrar_privada(nombre_sala, clave_sala, nombre_usuario):
    if nombre_sala not in salas_privadas:
        return gr.update(visible=True), gr.update(visible=False), "⚠️ La sala no existe."
    if clave_sala != salas_privadas[nombre_sala]["clave"]:
        return gr.update(visible=True), gr.update(visible=False), "⚠️ Clave incorrecta."
    if not nombre_usuario:
        return gr.update(visible=True), gr.update(visible=False), "⚠️ Escribe tu nombre."
    return gr.update(visible=False), gr.update(visible=True), f"✅ Bienvenido a {nombre_sala}, {nombre_usuario}."

def enviar_privada(nombre_sala, nombre_guardado, mensaje, clave_sala):
    if nombre_sala not in salas_privadas:
        return "⚠️ La sala no existe.", formatear_privada(nombre_sala, "")
    if not nombre_guardado or not mensaje:
        return "⚠️ Escribe tu nombre y un mensaje.", formatear_privada(nombre_sala, "")
    
    sala = salas_privadas[nombre_sala]
    if nombre_guardado in sala["usuarios"]:
        return f"⚠️ El nombre '{nombre_guardado}' ya está en uso.", formatear_privada(nombre_sala, clave_sala)
    
    clave_aes = hashlib.sha256(sala["clave"].encode()).digest()[:32]
    cifrado = cifrar(mensaje.encode(), clave_aes, 8)
    
    sala["mensajes"].append({
        "nombre": nombre_guardado,
        "cifrado": cifrado.hex().upper(),
        "hora": time.strftime("%H:%M")
    })
    sala["usuarios"].add(nombre_guardado)
    return "", formatear_privada(nombre_sala, clave_sala)

def ver_privada(nombre_sala, clave_ingresada):
    return formatear_privada(nombre_sala, clave_ingresada)

custom_css = """
body { background-color: #e5ddd5; }
.gradio-container { max-width: 800px; margin: auto; }
h1 { color: #075e54; text-align: center; font-family: 'Segoe UI', sans-serif; }
"""

with gr.Blocks(title="WhatsApp AES", css=custom_css) as demo:
    gr.Markdown("# 💬 Chat Cifrado con AES\n*Como WhatsApp, pero con cifrado AES.*")

    # Variable global para guardar el nombre del usuario
    nombre_guardado_gen = gr.State("")
    nombre_guardado_priv = gr.State("")

    with gr.Tabs():
        # --- PESTAÑA GENERAL ---
        with gr.Tab("🌍 General"):
            gr.Markdown("### Chat General\n*Todos ven el texto claro.*")
            
            with gr.Group(visible=True) as grupo_nombre_gen:
                nombre_gen = gr.Textbox(label="Tu nombre", placeholder="Ej. Gerardo")
                boton_entrar_gen = gr.Button("Entrar al chat", variant="primary")
            
            with gr.Group(visible=False) as grupo_chat_gen:
                chat_gen = gr.Chatbot(label="Chat", height=400)
                with gr.Row():
                    mensaje_gen = gr.Textbox(label="Mensaje", placeholder="Escribe algo...", scale=4)
                    boton_enviar_gen = gr.Button("Enviar", variant="primary", scale=1)
            
            estado_gen = gr.Markdown()
            
            boton_entrar_gen.click(
                entrar_general, 
                [nombre_gen], 
                [grupo_nombre_gen, grupo_chat_gen, estado_gen, nombre_guardado_gen]
            )
            boton_enviar_gen.click(
                enviar_general, 
                [nombre_guardado_gen, mensaje_gen], 
                [estado_gen, chat_gen]
            )
            mensaje_gen.submit(
                enviar_general, 
                [nombre_guardado_gen, mensaje_gen], 
                [estado_gen, chat_gen]
            )
            timer_gen = gr.Timer(3.0)
            timer_gen.tick(formatear_general, [], [chat_gen])

        # --- PESTAÑA PRIVADAS ---
        with gr.Tab("🔒 Salas Privadas"):
            gr.Markdown("### Salas Privadas\n*Cada sala tiene su clave.*")
            
            with gr.Group(visible=True) as grupo_entrada_priv:
                gr.Markdown("#### Crear sala")
                nombre_crear = gr.Textbox(label="Nombre de la sala", placeholder="Ej. ProyectoX")
                clave_crear = gr.Textbox(label="Clave", placeholder="Ej. 1234")
                boton_crear = gr.Button("Crear sala", variant="secondary")
                
                gr.Markdown("#### Entrar a una sala")
                nombre_entrar = gr.Textbox(label="Nombre de la sala", placeholder="Ej. ProyectoX")
                clave_entrar = gr.Textbox(label="Clave", placeholder="Ej. 1234", type="password")
                nombre_usuario_entrar = gr.Textbox(label="Tu nombre", placeholder="Ej. Gerardo")
                boton_entrar_priv = gr.Button("Entrar a la sala", variant="primary")
            
            with gr.Group(visible=False) as grupo_chat_priv:
                chat_priv = gr.Chatbot(label="Chat de la sala", height=400)
                with gr.Row():
                    mensaje_priv = gr.Textbox(label="Mensaje", placeholder="Escribe algo...", scale=4)
                    boton_enviar_priv = gr.Button("Enviar", variant="primary", scale=1)
            
            estado_priv = gr.Markdown()
            
            boton_crear.click(crear_privada, [nombre_crear, clave_crear], [estado_priv])
            boton_entrar_priv.click(
                entrar_privada, 
                [nombre_entrar, clave_entrar, nombre_usuario_entrar], 
                [grupo_entrada_priv, grupo_chat_priv, estado_priv, nombre_guardado_priv]
            )
            boton_enviar_priv.click(
                enviar_privada, 
                [nombre_entrar, nombre_guardado_priv, mensaje_priv, clave_entrar], 
                [estado_priv, chat_priv]
            )
            mensaje_priv.submit(
                enviar_privada, 
                [nombre_entrar, nombre_guardado_priv, mensaje_priv, clave_entrar], 
                [estado_priv, chat_priv]
            )
            timer_priv = gr.Timer(3.0)
            timer_priv.tick(ver_privada, [nombre_entrar, clave_entrar], [chat_priv])

demo.launch(server_name="0.0.0.0", server_port=int(os.environ.get("PORT", 7860)))
