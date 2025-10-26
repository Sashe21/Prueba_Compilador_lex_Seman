"""
COMPILADOR - AUTOMATAS 2
"""

import ply.lex as lex
import ply.yacc as yacc
import tkinter as tk
from tkinter import scrolledtext, ttk, filedialog, messagebox
from datetime import datetime
import os

# ================= DEFINICIÓN DE TOKENS =================
tokens = (
    'PROG','TIPO','TIPO_INT','TIPO_CAD','TIPO_BOOL', 'DECL', 'INICIO', 'FIN',
    'LEERDIG', 'IMPDIG', 'LEERCAD', 'IMPCAD',
    'LEERBOOL', 'IMPBOOL', 'FALS', 'VERD', 'SI',
    'SINO', 'PARA', 'MIENTRAS', 'UNION', 'INTER',
    'IN', 'OR', 'AND', 'NOT', 'PC', 'COMA', 'MAS',
    'MENOS', 'MUL', 'DIV', 'ASIG', 'PAREN', 'TESIS',
    'SIGMENOR', 'SIGMAYOR', 'IGUAL', 'SIGDIF',
    'ID', 'CINT', 'CAD', 'ERROR', 'ERROR_IDENTIFICADOR', 'ERROR_IDENTIFICADOR_SIM'
)

# Diccionario de palabras reservadas
reservadas = {
    'pf2024': ('PROG', 0),
    'Inicio': ('INICIO', 5),
    'Fin': ('FIN', 6),
    'Int': ('TIPO_INT', 1),
    'decl': ('DECL', 4),
    'Cad': ('TIPO_CAD', 2),
    'Bool': ('TIPO_BOOL', 3),
    'leerdig': ('LEERDIG', 7),
    'impdig': ('IMPDIG', 8),
    'Leercad': ('LEERCAD', 9),
    'impcad': ('IMPCAD', 10),
    'leerbol': ('LEERBOOL', 11),
    'Impbool': ('IMPBOOL', 12),
    'falso': ('FALS', 13),
    'verdadero': ('VERD', 14),
    'si': ('SI', 15),
    'sino': ('SINO', 16),
    'para': ('PARA', 17),
    'mientras': ('MIENTRAS', 18),
    'union': ('UNION', 19),
    'inter': ('INTER', 20),
    'in': ('IN', 21),
    'or': ('OR', 22),
    'and': ('AND', 23),
    'not': ('NOT', 24)
}

# ================= TOKENS SIMPLES =================
t_PC = r';'
t_COMA = r','
t_MAS = r'\+'
t_MENOS = r'-'
t_MUL = r'\*'
t_DIV = r'/'
t_ASIG = r':='
t_PAREN = r'\('
t_TESIS = r'\)'
t_SIGMENOR = r'<'
t_SIGMAYOR = r'>'
t_IGUAL = r'='
t_SIGDIF = r'<>'

# ================= VARIABLES GLOBALES =================
errores = []
errores_semanticos = []
tabla_simbolos = []
contador_simbolos = 1
arboles_operaciones = []
t_ignore = ' \t'
lineas_codigo = []
tabla_tipos = {}
temp_counter = 0
label_counter = 0
cuadruplos_globales = []
codigo_intermedio = []
nombre_programa = "programa"

# ================= CLASES PARA ANÁLISIS SEMÁNTICO =================

class ErrorSemantico:
    """Representa un error semántico encontrado durante el análisis"""
    def __init__(self, linea, tipo, descripcion, contexto, sugerencia=None):
        self.linea = linea
        self.tipo = tipo
        self.descripcion = descripcion
        self.contexto = contexto
        self.sugerencia = sugerencia

class Variable:
    """Representa una variable declarada en el programa"""
    def __init__(self, nombre, tipo, linea_declaracion, inicializada=False):
        self.nombre = nombre
        self.tipo = tipo
        self.linea_declaracion = linea_declaracion
        self.inicializada = inicializada
        self.usada = False
        self.lineas_uso = []
        self.valor = None

class AnalizadorSemantico:
    """Realiza el análisis semántico del código fuente"""
    def __init__(self):
        self.variables = {}
        self.variables_declaradas = set()
        self.variables_utilizadas = set()
        self.en_declaracion = False
        self.tipo_actual = None
        self.linea_actual = 1
        
    def reiniciar(self):
        """Reinicia el estado del analizador semántico"""
        self.variables = {}
        self.variables_declaradas = set()
        self.variables_utilizadas = set()
        self.en_declaracion = False
        self.tipo_actual = None
        self.linea_actual = 1

    def declarar_variable(self, nombre, tipo, linea):
        """Declara una nueva variable y verifica duplicados"""
        if nombre in self.variables:
            error = ErrorSemantico(
                linea=linea,
                tipo="VARIABLE_DUPLICADA",
                descripcion=f"La variable '{nombre}' ya fue declarada anteriormente",
                contexto=f"Primera declaración en línea {self.variables[nombre].linea_declaracion}",
                sugerencia=f"Use un nombre diferente o elimine la declaración duplicada"
            )
            errores_semanticos.append(error)
        else:
            self.variables[nombre] = Variable(nombre, tipo, linea)
            self.variables_declaradas.add(nombre)
    
    def usar_variable(self, nombre, linea):
        """Registra el uso de una variable y verifica que esté declarada"""
        if nombre not in self.variables:
            error = ErrorSemantico(
                linea=linea,
                tipo="VARIABLE_NO_DECLARADA",
                descripcion=f"La variable '{nombre}' no ha sido declarada",
                contexto=f"Se intenta usar '{nombre}' sin declaración previa",
                sugerencia=f"Declare la variable '{nombre}' en la sección 'decl' antes de usarla"
            )
            errores_semanticos.append(error)
            return None
        else:
            self.variables[nombre].usada = True
            self.variables[nombre].lineas_uso.append(linea)
            self.variables_utilizadas.add(nombre)
            return self.variables[nombre]
    
    def asignar_variable(self, nombre, tipo_expresion, linea):
        """Registra una asignación y verifica compatibilidad de tipos"""
        variable = self.usar_variable(nombre, linea)
        if variable:
            if tipo_expresion and variable.tipo != tipo_expresion:
                error = ErrorSemantico(
                    linea=linea,
                    tipo="INCOMPATIBILIDAD_TIPOS",
                    descripcion=f"Incompatibilidad de tipos en asignación",
                    contexto=f"Se intenta asignar tipo '{tipo_expresion}' a variable '{nombre}' de tipo '{variable.tipo}'",
                    sugerencia=f"Verifique que la expresión sea compatible con el tipo '{variable.tipo}'"
                )
                errores_semanticos.append(error)
            variable.inicializada = True
    
    def verificar_operacion_aritmetica(self, operandos, operador, linea):
        """Verifica que los operandos de una operación aritmética sean del tipo correcto"""
        tipo_esperado = "Int"
        for operando in operandos:
            if isinstance(operando, str) and operando in self.variables:
                variable = self.variables[operando]
                if variable.tipo != tipo_esperado:
                    error = ErrorSemantico(
                        linea=linea,
                        tipo="OPERACION_TIPO_INVALIDO",
                        descripcion=f"Operación aritmética '{operador}' no válida para tipo '{variable.tipo}'",
                        contexto=f"Variable '{operando}' de tipo '{variable.tipo}' en operación aritmética",
                        sugerencia=f"Use variables de tipo '{tipo_esperado}' en operaciones aritméticas"
                    )
                    errores_semanticos.append(error)
    
    def verificar_variables_no_utilizadas(self):
        """Verifica si hay variables declaradas pero no utilizadas"""
        for nombre, variable in self.variables.items():
            if not variable.usada:
                error = ErrorSemantico(
                    linea=variable.linea_declaracion,
                    tipo="VARIABLE_NO_UTILIZADA",
                    descripcion=f"La variable '{nombre}' fue declarada pero nunca utilizada",
                    contexto=f"Variable '{nombre}' de tipo '{variable.tipo}' declarada en línea {variable.linea_declaracion}",
                    sugerencia=f"Elimine la declaración de '{nombre}' si no la necesita, o úsela en el código"
                )
                errores_semanticos.append(error)
    
    def verificar_variables_no_inicializadas(self):
        """Verifica si hay variables usadas sin inicializar"""
        for nombre, variable in self.variables.items():
            if variable.usada and not variable.inicializada:
                error = ErrorSemantico(
                    linea=variable.lineas_uso[0] if variable.lineas_uso else variable.linea_declaracion,
                    tipo="VARIABLE_NO_INICIALIZADA",
                    descripcion=f"La variable '{nombre}' se usa sin haber sido inicializada",
                    contexto=f"Variable '{nombre}' usada en líneas {variable.lineas_uso} sin asignación previa",
                    sugerencia=f"Asigne un valor a '{nombre}' antes de usarla"
                )
                errores_semanticos.append(error)

analizador_sem = AnalizadorSemantico()

# ================= CLASES AUXILIARES =================
class NodoOperacion:
    """Representa un nodo en el árbol de sintaxis abstracta"""
    def __init__(self, tipo, valor=None, izquierdo=None, derecho=None, linea=None):
        self.tipo = tipo
        self.valor = valor
        self.izquierdo = izquierdo
        self.derecho = derecho
        self.linea = linea or 1
        self.tipo_dato = None

class SimboloTabla:
    """Representa un símbolo en la tabla de símbolos"""
    def __init__(self, lexema, token, referencia=None):
        global contador_simbolos
        self.numero = contador_simbolos
        self.lexema = lexema
        self.token = token
        self.referencia = referencia
        contador_simbolos += 1

# ================= FUNCIONES AUXILIARES =================
def agregar_simbolo(lexema, token, referencia=None):
    """Agrega un símbolo a la tabla de símbolos si no existe"""
    for simbolo in tabla_simbolos:
        if simbolo.lexema == lexema and simbolo.token == token:
            return simbolo
    nuevo_simbolo = SimboloTabla(lexema, token, referencia)
    tabla_simbolos.append(nuevo_simbolo)
    return nuevo_simbolo

def reiniciar_datos():
    """Reinicia todas las estructuras de datos globales"""
    global errores, errores_semanticos, tabla_simbolos, contador_simbolos, arboles_operaciones
    global lineas_codigo, tabla_tipos, temp_counter, label_counter, cuadruplos_globales, codigo_intermedio, nombre_programa
    errores = []
    errores_semanticos = []
    tabla_simbolos = []
    contador_simbolos = 1
    arboles_operaciones = []
    lineas_codigo = []
    tabla_tipos = {}
    temp_counter = 0
    label_counter = 0
    cuadruplos_globales = []
    codigo_intermedio = []
    nombre_programa = "programa"
    analizador_sem.reiniciar()

def obtener_linea_actual(p):
    """Obtiene el número de línea actual del parser"""
    try:
        if hasattr(p, 'lineno'):
            if hasattr(p.lineno, '__call__'):
                return p.lineno(1) if len(p) > 1 else 1
            else:
                return p.lineno
        elif len(p) > 1 and hasattr(p.slice[1], 'lineno'):
            return p.slice[1].lineno
        else:
            return 1
    except (AttributeError, IndexError):
        return 1

def nuevo_temp():
    """Genera un nuevo nombre de variable temporal"""
    global temp_counter
    temp_counter += 1
    return f"t{temp_counter}"

def nueva_etiqueta():
    """Genera una nueva etiqueta para saltos"""
    global label_counter
    label_counter += 1
    return f"L{label_counter}"

# ================= FUNCIONES DE TOKENS (ANALIZADOR LÉXICO) =================

def t_CINT(tok):
    r'\d+'
    tok.value = int(tok.value)
    return tok

def t_CAD(tok):
    r'"[^"]*"'
    return tok

def t_ID(t):
    r'[a-zA-Z][a-zA-Z0-9_]*'
    if t.value in reservadas:
        token_info = reservadas[t.value]
        t.type = token_info[0]
        t.ref = token_info[1]
    else:
        t.type = 'ID'
        t.ref = None
    return t

def t_ERROR_IDENTIFICADOR_NUM(t):
    r'\d+[a-zA-Z_]+[a-zA-Z0-9_]*'
    t.type = 'ERROR'
    errores.append({
        'line': t.lineno,
        'value': t.value,
        'type': 'ERROR_IDENTIFICADOR',
        'desc': 'Los identificadores no pueden empezar con números',
        'sugerencia': f"Cambie '{t.value}' por un nombre que empiece con letra, ej: 'var{t.value}'"
    })
    return t

def t_ERROR_IDENTIFICADOR(t):
    r'[a-zA-Z_][a-zA-Z0-9_]*[#$%&!]+[a-zA-Z0-9_]*|[a-zA-Z_]*[#$%&!]+[a-zA-Z0-9_]*'
    t.type = 'ERROR'
    caracteres_invalidos = ''.join(c for c in t.value if c in '#$%&!')
    errores.append({
        'line': t.lineno,
        'value': t.value,
        'type': 'ERROR_IDENTIFICADOR',
        'desc': f'Los identificadores solo pueden contener letras, números y guiones bajos',
        'sugerencia': f"Elimine los caracteres inválidos: {caracteres_invalidos}"
    })
    return t

def t_newline(tok):
    r'\n+'
    tok.lexer.lineno += len(tok.value)

def t_COMENTARIO(tok):
    r'/\*[^*]*\*+(?:[^/*][^*]*\*+)*/|//.*'
    tok.lexer.lineno += tok.value.count('\n')
    pass

def t_error(t):
    """Maneja errores léxicos"""
    errores.append({
        'line': t.lineno,
        'value': t.value[0],
        'type': 'ERROR_LEXICO',
        'desc': f'Carácter ilegal "{t.value[0]}"',
        'sugerencia': f'Elimine o reemplace el carácter "{t.value[0]}"'
    })
    t.lexer.skip(1)

analizador_lexico = lex.lex()

# ================= ANALIZADOR SINTÁCTICO =================

precedence = (
    ('left', 'MAS', 'MENOS'),
    ('left', 'MUL', 'DIV'),
    ('right', 'UMINUS'),
)

# ================= REGLAS GRAMATICALES =================

def p_programa(p):
    '''programa : PROG ID programa_decl'''
    global nombre_programa
    nombre_programa = p[2]
    agregar_simbolo(p[1], 'PROG', 'Palabra clave del programa')
    agregar_simbolo(p[2], 'ID', 'Nombre del programa')
    analizador_sem.verificar_variables_no_utilizadas()
    analizador_sem.verificar_variables_no_inicializadas()

def p_programa_decl(p):
    '''programa_decl : declaraciones cuerpo_programa
                    | cuerpo_programa'''
    pass

def p_declaraciones(p):
    '''declaraciones : DECL lista_declaraciones'''
    agregar_simbolo(p[1], 'DECL', 'Sección de declaraciones')

def p_lista_declaraciones(p):
    '''lista_declaraciones : declaracion lista_declaraciones
                          | declaracion'''
    pass

def p_declaracion(p):
    '''declaracion : tipo lista_variables PC'''
    agregar_simbolo(';', 'PC', 'Fin de declaración')

def p_tipo(p):
    '''tipo : TIPO_INT
           | TIPO_CAD
           | TIPO_BOOL'''
    if p[1] == 'Int':
        agregar_simbolo('Int', 'TIPO_INT', 'Tipo de dato entero')
        analizador_sem.tipo_actual = 'Int'
    elif p[1] == 'Cad':
        agregar_simbolo('Cad', 'TIPO_CAD', 'Tipo de dato cadena')
        analizador_sem.tipo_actual = 'Cad'
    elif p[1] == 'Bool':
        agregar_simbolo('Bool', 'TIPO_BOOL', 'Tipo de dato booleano')
        analizador_sem.tipo_actual = 'Bool'

def p_lista_variables(p):
    '''lista_variables : ID COMA lista_variables
                      | ID'''
    linea = obtener_linea_actual(p)
    
    if len(p) == 2:
        agregar_simbolo(p[1], 'ID', 'Variable')
        analizador_sem.declarar_variable(p[1], analizador_sem.tipo_actual, linea)
    else:
        agregar_simbolo(p[1], 'ID', 'Variable')
        agregar_simbolo(',', 'COMA', 'Separador de variables')
        analizador_sem.declarar_variable(p[1], analizador_sem.tipo_actual, linea)

def p_cuerpo_programa(p):
    '''cuerpo_programa : INICIO instrucciones FIN'''
    agregar_simbolo('Inicio', 'INICIO', 'Inicio del programa')
    agregar_simbolo('Fin', 'FIN', 'Fin del programa')

def p_instrucciones(p):
    '''instrucciones : instruccion instrucciones
                    | instruccion'''
    pass

def p_instruccion(p):
    '''instruccion : asignacion
                  | llamada_funcion
                  | estructura_control'''
    pass

def p_estructura_control(p):
    '''estructura_control : si_entonces
                         | mientras_hacer
                         | para_hacer'''
    pass

def p_si_entonces(p):
    '''si_entonces : SI PAREN expresion TESIS instruccion
                  | SI PAREN expresion TESIS instruccion SINO instruccion'''
    linea = obtener_linea_actual(p)
    
    agregar_simbolo('si', 'SI', 'Estructura condicional')
    
    etiq_falso = nueva_etiqueta()
    etiq_fin = nueva_etiqueta()
    
    # Generar cuádruplo para la condición del if
    condicion_result, cond_quads = generar_cuadruplos_desde_nodo(p[3], [])
    cuadruplos_globales.extend(cond_quads)

    # Si la condición es falsa, salta a la etiqueta de falso (o sino)
    cuadruplos_globales.append(('if_false', condicion_result, None, etiq_falso))
    
    # Ejecutar la instrucción del 'si'
    instruccion_result, instruccion_quads = generar_cuadruplos_desde_nodo(p[4], [])
    cuadruplos_globales.extend(instruccion_quads)

    if len(p) == 6: # Con 'sino'
        # Si hay 'sino', salta incondicionalmente al final
        cuadruplos_globales.append(('goto', None, None, etiq_fin))
        # Etiqueta para el 'sino'
        cuadruplos_globales.append(('label', None, None, etiq_falso))
        # Ejecutar la instrucción del 'sino'
        sino_result, sino_quads = generar_cuadruplos_desde_nodo(p[5], [])
        cuadruplos_globales.extend(sino_quads)
    
    # Etiqueta para el final del if (o el fin del 'sino')
    cuadruplos_globales.append(('label', None, None, etiq_fin))

def p_mientras_hacer(p):
    '''mientras_hacer : MIENTRAS PAREN expresion TESIS instruccion'''
    agregar_simbolo('mientras', 'MIENTRAS', 'Estructura de repetición')
    
    etiq_inicio = nueva_etiqueta()
    etiq_fin = nueva_etiqueta()
    
    # Etiqueta de inicio del bucle
    cuadruplos_globales.append(('label', None, None, etiq_inicio))
    
    # Generar cuádruplos para la condición
    condicion_result, cond_quads = generar_cuadruplos_desde_nodo(p[3], [])
    cuadruplos_globales.extend(cond_quads)
    
    # Si la condición es falsa, salta al final del bucle
    cuadruplos_globales.append(('if_false', condicion_result, None, etiq_fin))
    
    # Ejecutar la instrucción del 'mientras'
    instruccion_result, instruccion_quads = generar_cuadruplos_desde_nodo(p[4], [])
    cuadruplos_globales.extend(instruccion_quads)
    
    # Volver al inicio del bucle
    cuadruplos_globales.append(('goto', None, None, etiq_inicio))
    
    # Etiqueta de fin del bucle
    cuadruplos_globales.append(('label', None, None, etiq_fin))

def p_para_hacer(p):
    '''para_hacer : PARA PAREN asignacion expresion PC expresion TESIS instruccion'''
    agregar_simbolo('para', 'PARA', 'Estructura de repetición')
    
    etiq_inicio = nueva_etiqueta()
    etiq_fin = nueva_etiqueta()
    
    # Generar cuádruplos para la asignación inicial
    asignacion_result, asignacion_quads = generar_cuadruplos_desde_nodo(p[3], [])
    cuadruplos_globales.extend(asignacion_quads)
    
    # Etiqueta de inicio del bucle
    cuadruplos_globales.append(('label', None, None, etiq_inicio))
    
    # Generar cuádruplos para la condición de continuación
    condicion_result, cond_quads = generar_cuadruplos_desde_nodo(p[4], [])
    cuadruplos_globales.extend(cond_quads)
    
    # Si la condición es falsa, salta al final del bucle
    cuadruplos_globales.append(('if_false', condicion_result, None, etiq_fin))
    
    # Ejecutar la instrucción del 'para'
    instruccion_result, instruccion_quads = generar_cuadruplos_desde_nodo(p[7], [])
    cuadruplos_globales.extend(instruccion_quads)
    
    # Generar cuádruplos para la actualización
    actualizacion_result, actualizacion_quads = generar_cuadruplos_desde_nodo(p[6], [])
    cuadruplos_globales.extend(actualizacion_quads)
    
    # Volver al inicio del bucle
    cuadruplos_globales.append(('goto', None, None, etiq_inicio))
    
    # Etiqueta de fin del bucle
    cuadruplos_globales.append(('label', None, None, etiq_fin))

def p_asignacion(p):
    '''asignacion : ID ASIG expresion PC'''
    linea = obtener_linea_actual(p)
    
    agregar_simbolo(p[1], 'ID', 'Variable en asignación')
    agregar_simbolo(':=', 'ASIG', 'Operador de asignación')
    agregar_simbolo(';', 'PC', 'Fin de instrucción')
    
    tipo_expresion = None
    if p[3]:
        tipo_expresion = getattr(p[3], 'tipo_dato', 'Int')
    
    analizador_sem.asignar_variable(p[1], tipo_expresion, linea)
    
    if p[3] and hasattr(p[3], 'tipo') and p[3].tipo in ['operacion', 'termino', 'ID', 'CAD']:
        valor, tipo_eval = evaluar_nodo(p[3])
        var = analizador_sem.variables.get(p[1])
        if valor is not None and var is not None:
            var.valor = valor
            var.inicializada = True

        resultado_operando, quads = generar_cuadruplos_desde_nodo(p[3], [])

        asign_dest = p[1]
        if resultado_operando is not None:
            quads.append((':=', resultado_operando, None, asign_dest))

        cuadruplos_globales.extend(quads)

        arboles_operaciones.append({
            'variable': p[1],
            'expresion': p[3],
            'linea': linea,
            'resultado': valor,
            'tipo_resultado': tipo_eval,
            'cuadruplos': quads
        })

def p_expresion_binaria(p):
    '''expresion : expresion MAS expresion
                | expresion MENOS expresion
                | expresion MUL expresion
                | expresion DIV expresion'''
    linea = obtener_linea_actual(p)
    
    operandos = []
    # Procesar operandos para la verificación semántica
    if hasattr(p[1], 'valor'):
        if isinstance(p[1].valor, str) and p[1].valor in analizador_sem.variables:
            operandos.append(p[1].valor)
        elif isinstance(p[1].valor, int):
            operandos.append(p[1].valor)
    if hasattr(p[3], 'valor'):
        if isinstance(p[3].valor, str) and p[3].valor in analizador_sem.variables:
            operandos.append(p[3].valor)
        elif isinstance(p[3].valor, int):
            operandos.append(p[3].valor)
    
    analizador_sem.verificar_operacion_aritmetica(operandos, p[2], linea)
    
    if p[2] == '+':
        agregar_simbolo('+', 'MAS', 'Operador suma')
        p[0] = NodoOperacion('operacion', '+', p[1], p[3], linea)
    elif p[2] == '-':
        agregar_simbolo('-', 'MENOS', 'Operador resta')
        p[0] = NodoOperacion('operacion', '-', p[1], p[3], linea)
    elif p[2] == '*':
        agregar_simbolo('*', 'MUL', 'Operador multiplicación')
        p[0] = NodoOperacion('operacion', '*', p[1], p[3], linea)
    elif p[2] == '/':
        agregar_simbolo('/', 'DIV', 'Operador división')
        p[0] = NodoOperacion('operacion', '/', p[1], p[3], linea)
        
        # Verificación de división por cero en tiempo de compilación si es constante
        if p[3] and hasattr(p[3], 'tipo') and p[3].tipo == 'termino':
            try:
                valor_divisor = int(p[3].valor)
                if valor_divisor == 0:
                    error = ErrorSemantico(
                        linea=linea,
                        tipo="DIVISION_POR_CERO",
                        descripcion="⚠️ Posible división por cero detectada",
                        contexto=f"División por constante cero en línea {linea}",
                        sugerencia="Verifique que el divisor no sea cero antes de realizar la división"
                    )
                    errores_semanticos.append(error)
            except ValueError:
                pass # No es un número entero constante
    
    p[0].tipo_dato = 'Int'

def p_expresion_unaria(p):
    '''expresion : MENOS expresion %prec UMINUS'''
    linea = obtener_linea_actual(p)
    agregar_simbolo('-', 'MENOS', 'Operador menos unario')
    p[0] = NodoOperacion('operacion', '-', None, p[2], linea)
    p[0].tipo_dato = 'Int'

def p_expresion_parentesis(p):
    '''expresion : PAREN expresion TESIS'''
    agregar_simbolo('(', 'PAREN', 'Paréntesis izquierdo')
    agregar_simbolo(')', 'TESIS', 'Paréntesis derecho')
    p[0] = p[2]

def p_expresion_factor(p):
    '''expresion : ID
                | CINT
                | CAD'''
    linea = obtener_linea_actual(p)
    
    if isinstance(p[1], int):
        agregar_simbolo(str(p[1]), 'CINT', 'Constante entera')
        p[0] = NodoOperacion('termino', str(p[1]), None, None, linea)
        p[0].tipo_dato = 'Int'
    elif isinstance(p[1], str) and p[1].startswith('"') and p[1].endswith('"'):
        agregar_simbolo(p[1], 'CAD', 'Literal de cadena')
        p[0] = NodoOperacion('CAD', p[1], None, None, linea)
        p[0].tipo_dato = 'Cad'
    else:
        agregar_simbolo(p[1], 'ID', 'Variable en expresión')
        variable = analizador_sem.usar_variable(p[1], linea)
        p[0] = NodoOperacion('ID', p[1], None, None, linea)
        p[0].tipo_dato = variable.tipo if variable else 'Int'

def p_llamada_funcion(p):
    '''llamada_funcion : IMPCAD PAREN parametro TESIS PC
                      | IMPDIG PAREN parametro TESIS PC
                      | LEERDIG PAREN ID TESIS PC'''
    linea = obtener_linea_actual(p)
    
    if p[1] in ('impcad', 'impdig'):
        token = 'IMPCAD' if p[1] == 'impcad' else 'IMPDIG'
        descripcion = 'Función imprimir cadena' if p[1] == 'impcad' else 'Función imprimir dígito'
        agregar_simbolo(p[1], token, descripcion)
    
        parametro_nodo = None
        if p[3]:
            parametro_nodo = generar_cuadruplos_desde_nodo(p[3])[0] if isinstance(p[3], NodoOperacion) else p[3]
        
        # Generar cuádruplo para la llamada a función
        cuadruplos_globales.append((p[1], parametro_nodo, None, None))

        if p[1] == 'impdig':
            if p[3] is not None:
                if isinstance(p[3], str) and p[3].startswith('"') and p[3].endswith('"'):
                    # Intentando imprimir una cadena literal con impdig
                    error = ErrorSemantico(
                        linea=linea,
                        tipo="PARAMETRO_TIPO_INCORRECTO",
                        descripcion=f"❌ La función 'impdig' requiere parámetro de tipo 'Int'",
                        contexto=f"Se pasó una cadena literal a la función 'impdig'",
                        sugerencia="Use una variable de tipo 'Int' o un número entero"
                    )
                    errores_semanticos.append(error)
                else:
                    # Verificación de tipo para variable
                    variable = analizador_sem.variables.get(p[3])
                    if variable and variable.tipo != 'Int':
                        error = ErrorSemantico(
                            linea=linea,
                            tipo="PARAMETRO_TIPO_INCORRECTO",
                            descripcion=f"❌ La función 'impdig' requiere parámetro de tipo 'Int'",
                            contexto=f"Se pasó variable '{p[3]}' de tipo '{variable.tipo}' a función 'impdig'",
                            sugerencia="Use una variable de tipo 'Int' o un número entero"
                        )
                        errores_semanticos.append(error)
        
        elif p[1] == 'impcad':
            if p[3] is not None:
                if isinstance(p[3], int) or isinstance(p[3], NodoOperacion) and p[3].tipo_dato == 'Int':
                    # Intentando imprimir un entero con impcad
                    error = ErrorSemantico(
                        linea=linea,
                        tipo="PARAMETRO_TIPO_INCORRECTO",
                        descripcion=f"❌ La función 'impcad' requiere parámetro de tipo 'Cad'",
                        contexto=f"Se pasó un entero a la función 'impcad'",
                        sugerencia="Use una variable de tipo 'Cad' o una cadena literal"
                    )
                    errores_semanticos.append(error)
                else:
                    # Verificación de tipo para variable
                    variable = analizador_sem.variables.get(p[3])
                    if variable and variable.tipo != 'Cad':
                        error = ErrorSemantico(
                            linea=linea,
                            tipo="PARAMETRO_TIPO_INCORRECTO",
                            descripcion=f"❌ La función 'impcad' requiere parámetro de tipo 'Cad'",
                            contexto=f"Se pasó variable '{p[3]}' de tipo '{variable.tipo}' a función 'impcad'",
                            sugerencia="Use una variable de tipo 'Cad' o una cadena literal"
                        )
                        errores_semanticos.append(error)
            
    elif p[1] == 'leerdig':
        agregar_simbolo('leerdig', 'LEERDIG', 'Función leer dígito')
        
        # Generar cuádruplo para la lectura y asignación
        cuadruplos_globales.append(('leerdig', None, None, p[3]))
        
        if p[3] is not None:
            # Verificación de tipo para la variable de destino
            variable = analizador_sem.variables.get(p[3])
            if variable and variable.tipo != 'Int':
                error = ErrorSemantico(
                    linea=linea,
                    tipo="PARAMETRO_TIPO_INCORRECTO",
                    descripcion=f"❌ La función 'leerdig' requiere variable de tipo 'Int'",
                    contexto=f"Se pasó variable '{p[3]}' de tipo '{variable.tipo}' a función 'leerdig'",
                    sugerencia="Use una variable de tipo 'Int'"
                )
                errores_semanticos.append(error)
            else:
                if variable:
                    variable.inicializada = True
    
    agregar_simbolo('(', 'PAREN', 'Paréntesis izquierdo')
    agregar_simbolo(')', 'TESIS', 'Paréntesis derecho')
    agregar_simbolo(';', 'PC', 'Fin de instrucción')

def p_parametro(p):
    '''parametro : CAD
                | ID'''
    if p[1].startswith('"') and p[1].endswith('"'):
        agregar_simbolo(p[1], 'CAD', 'Literal de cadena')
        p[0] = p[1] # Retorna el valor literal de la cadena
    else:
        agregar_simbolo(p[1], 'ID', 'Variable como parámetro')
        p[0] = p[1] # Retorna el nombre de la variable

def p_error(p):
    """Maneja errores sintácticos"""
    try:
        if p:
            token_descripcion = obtener_descripcion_token(p.type, p.value)
            linea = getattr(p, 'lineno', 'desconocida')
            
            contexto = ""
            if linea != 'desconocida' and linea <= len(lineas_codigo):
                contexto = f"\n   Línea {linea}: {lineas_codigo[linea-1].strip()}"
            
            errores.append({
                'line': linea,
                'value': str(p.value) if p.value is not None else 'None',
                'type': 'ERROR_SINTACTICO',
                'desc': f"Error de sintaxis: se encontró {token_descripcion}{contexto}",
                'sugerencia': obtener_sugerencia_sintactica(p.type)
            })
        else:
            errores.append({
                'line': 'EOF',
                'value': 'EOF',
                'type': 'ERROR_SINTACTICO',
                'desc': "Error de sintaxis: fin de archivo inesperado. Verifique que el programa esté completo.",
                'sugerencia': "Asegúrese de que el programa tenga la estructura: pf2024 nombre ... Inicio ... Fin"
            })
    except Exception as e:
        errores.append({
            'line': 'desconocida',
            'value': 'error_interno',
            'type': 'ERROR_SINTACTICO',
            'desc': "Error de sintaxis: error interno del parser",
            'sugerencia': "Revise la estructura general del programa"
        })

def obtener_descripcion_token(tipo_token, valor_token):
    """Obtiene una descripción legible del token para mensajes de error"""
    descripciones = {
        'TESIS': 'paréntesis de cierre ")"',
        'PAREN': 'paréntesis de apertura "("',
        'PC': 'punto y coma ";"',
        'ID': f'identificador "{valor_token}"',
        'CINT': f'número "{valor_token}"',
        'CAD': f'cadena "{valor_token}"',
        'ASIG': 'operador de asignación ":="',
        'FIN': 'palabra clave "Fin"',
        'INICIO': 'palabra clave "Inicio"',
    }
    return descripciones.get(tipo_token, f'token {tipo_token} con valor "{valor_token}"')

def obtener_sugerencia_sintactica(tipo_token):
    """Proporciona sugerencias específicas según el tipo de error"""
    sugerencias = {
        'PC': 'Agregue un punto y coma ";" al final de la instrucción',
        'TESIS': 'Cierre el paréntesis con ")"',
        'PAREN': 'Abra el paréntesis con "("',
        'FIN': 'Termine el programa con la palabra "Fin"',
        'INICIO': 'Inicie el cuerpo del programa con "Inicio"',
    }
    return sugerencias.get(tipo_token, 'Revise la sintaxis del programa')

parser = yacc.yacc()

# ================= FUNCIONES PARA EVALUACIÓN Y GENERACIÓN DE CÓDIGO =================

def expresion_a_texto(nodo, precedencia_padre=0):
    """Convierte un árbol de expresión a texto legible"""
    if nodo is None:
        return ""
    precedencias = {'+': 1, '-': 1, '*': 2, '/': 2}
    if nodo.tipo == 'operacion':
        precedencia_actual = precedencias.get(nodo.valor, 0)
        if nodo.izquierdo is None: # Operación unaria
            der_texto = expresion_a_texto(nodo.derecho, precedencia_actual)
            expresion = f"{nodo.valor}{der_texto}"
        else: # Operación binaria
            izq_texto = expresion_a_texto(nodo.izquierdo, precedencia_actual)
            der_texto = expresion_a_texto(nodo.derecho, precedencia_actual)
            expresion = f"{izq_texto} {nodo.valor} {der_texto}"
        
        if precedencia_actual < precedencia_padre:
            expresion = f"({expresion})"
        return expresion
    elif nodo.tipo in ('termino', 'ID', 'CAD'):
        # Maneja constantes numéricas (termino), variables (ID) y cadenas literales (CAD)
        return str(nodo.valor)
    return str(nodo.valor)

def imprimir_arbol_operacion(nodo, nivel=0):
    """Imprime el árbol de operaciones de forma jerárquica"""
    if nodo is None:
        return ""
    indentacion = "  " * nivel
    resultado = ""
    if nodo.tipo == 'operacion':
        resultado += f"{indentacion}operacion: {nodo.valor}\n"
        if nodo.izquierdo:
            resultado += imprimir_arbol_operacion(nodo.izquierdo, nivel + 1)
        if nodo.derecho:
            resultado += imprimir_arbol_operacion(nodo.derecho, nivel + 1)
    elif nodo.tipo == 'termino':
        resultado += f"{indentacion}termino: {nodo.valor}\n"
    elif nodo.tipo == 'ID':
        resultado += f"{indentacion}ID: {nodo.valor}\n"
    elif nodo.tipo == 'CAD':
        resultado += f"{indentacion}CAD: {nodo.valor}\n"
    return resultado

def evaluar_nodo(nodo):
    """Evalúa un nodo del árbol y retorna su valor y tipo"""
    if nodo is None:
        return None, None
    if nodo.tipo == 'termino': # Constante entera
        try:
            v = int(nodo.valor)
            return v, 'Int'
        except Exception:
            return None, None
    if nodo.tipo == 'CAD': # Cadena literal
        return nodo.valor, 'Cad'
    if nodo.tipo == 'ID': # Variable
        nombre = nodo.valor
        var = analizador_sem.variables.get(nombre)
        if var is None or not var.inicializada:
            return None, None # No está inicializada o no existe
        return var.valor, var.tipo
    if nodo.tipo == 'operacion':
        op = nodo.valor
        if nodo.izquierdo is None: # Operación unaria
            rv, rt = evaluar_nodo(nodo.derecho)
            if rv is None or rt != 'Int':
                return None, None
            if op == '-':
                return -rv, 'Int'
            return None, None
        
        # Operación binaria
        lv, lt = evaluar_nodo(nodo.izquierdo)
        rv, rt = evaluar_nodo(nodo.derecho)
        
        if lv is None or rv is None:
            return None, None # Uno de los operandos no se pudo evaluar

        # Verificar compatibilidad de tipos para operaciones aritméticas
        if lt != 'Int' or rt != 'Int':
            # Aquí se podría añadir un error semántico si se permite la mezcla de tipos
            # Por ahora, solo retornamos None si no son ambos 'Int'
            return None, None
        
        try:
            if op == '+':
                return lv + rv, 'Int'
            elif op == '-':
                return lv - rv, 'Int'
            elif op == '*':
                return lv * rv, 'Int'
            elif op == '/':
                if rv == 0:
                    return None, None # División por cero
                return lv // rv, 'Int' # División entera
        except Exception:
            return None, None
    return None, None

def generar_cuadruplos_desde_nodo(nodo, quads=None):
    """Genera cuádruplos (código intermedio) desde un nodo del árbol"""
    if quads is None:
        quads = []
    if nodo is None:
        return None, quads
    if nodo.tipo == 'termino': # Constante entera
        return nodo.valor, quads
    if nodo.tipo == 'CAD': # Cadena literal
        return nodo.valor, quads
    if nodo.tipo == 'ID': # Variable
        return nodo.valor, quads
    
    if nodo.tipo == 'operacion':
        op = nodo.valor
        
        if nodo.izquierdo is None: # Operación unaria
            operando_d, quads = generar_cuadruplos_desde_nodo(nodo.derecho, quads)
            t = nuevo_temp()
            quads.append((op, operando_d, None, t))
            return t, quads
        else: # Operación binaria
            left_operand, quads = generar_cuadruplos_desde_nodo(nodo.izquierdo, quads)
            right_operand, quads = generar_cuadruplos_desde_nodo(nodo.derecho, quads)
            t = nuevo_temp()
            quads.append((op, left_operand, right_operand, t))
            return t, quads
    return None, quads

def generar_codigo_intermedio_formateado():
    """Genera código intermedio en formato de tres direcciones legible"""
    global codigo_intermedio
    codigo_intermedio = []
    
    if not cuadruplos_globales:
        return "⚠️ No se generó código intermedio.\n"
    
    resultado =  "╔═══════════════════════════════════════════════════════════╗\n"
    resultado += "║          CÓDIGO INTERMEDIO DE TRES DIRECCIONES           ║\n"
    resultado += "╚═══════════════════════════════════════════════════════════╝\n\n"
    
    for i, cuad in enumerate(cuadruplos_globales, 1):
        op, arg1, arg2, res = cuad
        linea_num = f"{i:03d}"
        
        if op == ':=':
            linea_codigo = f"{linea_num}: {res} = {arg1}"
        elif op in ['+', '-', '*', '/']:
            if arg2 is None: # Operación unaria
                linea_codigo = f"{linea_num}: {res} = {op}{arg1}"
            else: # Operación binaria
                linea_codigo = f"{linea_num}: {res} = {arg1} {op} {arg2}"
        elif op == 'impcad':
            linea_codigo = f"{linea_num}: print({arg1})"
        elif op == 'impdig':
            linea_codigo = f"{linea_num}: print({arg1})"
        elif op == 'leerdig':
            linea_codigo = f"{linea_num}: read({res})"
        elif op == 'label':
            linea_codigo = f"{linea_num}: {res}:"
        elif op == 'goto':
            linea_codigo = f"{linea_num}: goto {res}"
        elif op == 'if_false':
            linea_codigo = f"{linea_num}: if_false {arg1} goto {res}"
        else:
            linea_codigo = f"{linea_num}: {op} {arg1} {arg2} {res}"
        
        codigo_intermedio.append(linea_codigo)
        resultado += linea_codigo + "\n"
    
    resultado += "\n" + "─" * 60 + "\n"
    resultado += f"✓ Total de instrucciones: {len(cuadruplos_globales)}\n"
    
    return resultado

def generar_reporte_semantico():
    """Genera un reporte completo del análisis semántico"""
    if not errores_semanticos and not analizador_sem.variables:
        return "⚠️ No se realizó análisis semántico."
    
    resultado = "╔═══════════════════════════════════════════════════════════╗\n"
    resultado += "║              REPORTE DE ANÁLISIS SEMÁNTICO                ║\n"
    resultado += "╚═══════════════════════════════════════════════════════════╝\n\n"
    
    resultado += "┌─ TABLA DE VARIABLES DECLARADAS ─────────────────────────┐\n"
    if analizador_sem.variables:
        resultado += f"│ {'Variable':<15} {'Tipo':<8} {'Línea':<6} {'Inic.':<6} {'Usada':<6} │\n"
        resultado += "├" + "─"*58 + "┤\n"
        for nombre, var in sorted(analizador_sem.variables.items()): # Ordenar por nombre
            inicializada = "✓" if var.inicializada else "✗"
            usada = "✓" if var.usada else "✗"
            resultado += f"│ {nombre:<15} {var.tipo:<8} {var.linea_declaracion:<6} {inicializada:<6} {usada:<6} │\n"
    else:
        resultado += "│ No se encontraron variables declaradas.                  │\n"
    resultado += "└" + "─"*58 + "┘\n\n"
    
    resultado += "┌─ ESTADÍSTICAS ──────────────────────────────────────────┐\n"
    resultado += f"│ Variables declaradas: {len(analizador_sem.variables):<35} │\n"
    resultado += f"│ Variables utilizadas: {len(analizador_sem.variables_utilizadas):<35} │\n"
    resultado += f"│ Errores semánticos:   {len(errores_semanticos):<35} │\n"
    resultado += "└" + "─"*58 + "┘\n\n"
    
    if errores_semanticos:
        resultado += "┌─ ERRORES SEMÁNTICOS ────────────────────────────────────┐\n"
        for i, error in enumerate(errores_semanticos, 1):
            resultado += f"│ ❌ Error #{i}:\n"
            resultado += f"│   📍 Línea: {error.linea}\n"
            resultado += f"│   🏷️  Tipo: {error.tipo}\n"
            resultado += f"│   📝 {error.descripcion}\n"
            resultado += f"│   📄 Contexto: {error.contexto}\n"
            if error.sugerencia:
                resultado += f"│   💡 Sugerencia: {error.sugerencia}\n"
            resultado += "│\n"
        resultado += "└" + "─"*58 + "┘\n"
    else:
        resultado += "✅ No se encontraron errores semánticos.\n\n"
    
    return resultado

def generar_codigo_ensamblador_emu8086():
    """Genera código ensamblador compatible con emu8086 (16-bit, DOS)"""
    if not cuadruplos_globales:
        return "; No se generaron cuádruplos.\n"
    
    resultado = "; ═══════════════════════════════════════════════════════════\n"
    resultado += f"; CÓDIGO ENSAMBLADOR PARA EMU8086 - {nombre_programa.upper()}\n"
    resultado += f"; Generado: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n"
    resultado += "; Arquitectura: 8086 (16-bit)\n"
    resultado += "; Compatible con: emu8086, DOSBox\n"
    resultado += "; ═══════════════════════════════════════════════════════════\n\n"
    
    # Directivas del procesador
    resultado += ".MODEL SMALL\n"
    resultado += ".STACK 100h\n\n"
    
    # Sección de datos
    resultado += ".DATA\n"
    resultado += "    ; Variables del programa\n"
    
    # Declarar variables del usuario
    for nombre, var in analizador_sem.variables.items():
        if var.tipo == 'Int':
            # Inicializar a 0 si no está inicializada, o usar su valor si lo está
            valor_inicial = f"{var.valor}" if var.inicializada else "0"
            resultado += f"    {nombre} DW {valor_inicial}          ; Variable entera\n"
        elif var.tipo == 'Cad':
            # Las cadenas se manejan de forma diferente, esta es una declaración genérica
            # El contenido real se manejará en el código de impresión/lectura
            resultado += f"    {nombre} DB 256 DUP('$')  ; Variable cadena\n"
    
    # Variables temporales
    if temp_counter > 0:
        resultado += "\n    ; Variables temporales (DW para Word - 16 bits)\n"
        for i in range(1, temp_counter + 1):
            resultado += f"    t{i} DW 0\n"
    
    # Mensajes y constantes
    resultado += "\n    ; Mensajes del sistema\n"
    resultado += "    newline DB 0Dh, 0Ah, '$'\n"
    resultado += "    buffer DB 10 DUP('$') ; Buffer para lectura de cadenas (no implementado)\n"
    
    # Buscar cadenas literales en los cuádruplos
    cadenas_literales = {}
    contador_cadenas = 0
    for cuad in cuadruplos_globales:
        op, arg1, arg2, res = cuad
        if op == 'impcad' and arg1 and isinstance(arg1, str) and arg1.startswith('"'):
            if arg1 not in cadenas_literales:
                contador_cadenas += 1
                label_cadena = f"str{contador_cadenas}"
                cadenas_literales[arg1] = label_cadena
                # Remover comillas y agregar terminador $
                contenido = arg1[1:-1]
                resultado += f"    {label_cadena} DB '{contenido}', '$'\n"
    
    # Sección de código
    resultado += "\n.CODE\n"
    resultado += "MAIN PROC\n"
    resultado += "    MOV AX, @DATA\n"
    resultado += "    MOV DS, AX\n\n"
    
    # Generar código para cada cuádruplo
    for i, cuad in enumerate(cuadruplos_globales, 1):
        op, arg1, arg2, res = cuad
        resultado += f"    ; ─── Cuádruplo {i}: {op} {arg1 or ''} {arg2 or ''} {res or ''} ───\n"
        
        if op == ':=':
            # Asignación: se usa AX como registro temporal
            # Cargar el valor del operando en AX
            if isinstance(arg1, int):
                resultado += f"    MOV AX, {arg1}\n"
            elif isinstance(arg1, str) and arg1.startswith('"') and arg1.endswith('"'):
                # Asignar una cadena literal (requiere manejo de cadenas, por ahora simplificado a un solo carácter)
                # Para asignación de cadenas completas, se necesitaría un bucle o un movsb
                if len(arg1) == 3: # Solo el carácter y las comillas, ej: '"a"'
                     resultado += f"    MOV AL, {arg1}\n" # Carga el carácter en AL
                     resultado += f"    MOV AH, 0\n"     # Limpia AH
                else:
                    # Manejo de cadenas más largas es complejo para esta versión simple
                    # Se asignará solo el primer carácter o se asumirá un valor por defecto
                    # Para propósitos de emu8086, a menudo se trabaja con bytes o palabras
                    # Aquí simplificamos a un solo byte para la asignación simple
                    if len(arg1) >= 3:
                        char_literal = arg1[1] # Primer carácter
                        resultado += f"    MOV AL, '{char_literal}'\n"
                        resultado += f"    MOV AH, 0\n"
                    else: # Cadena vacía
                        resultado += f"    MOV AX, 0\n"
            else: # Variable o temporal
                resultado += f"    MOV AX, {arg1}\n"
            
            # Almacenar AX en el destino
            resultado += f"    MOV {res}, AX\n"
            
        elif op == '+':
            # Suma: Se asume que arg1 y arg2 son números o variables de tipo Int
            # Cargar arg1 en AX
            if isinstance(arg1, int):
                resultado += f"    MOV AX, {arg1}\n"
            else:
                resultado += f"    MOV AX, {arg1}\n"
            
            # Sumar arg2 a AX
            if isinstance(arg2, int):
                resultado += f"    ADD AX, {arg2}\n"
            else:
                resultado += f"    ADD AX, {arg2}\n"
            
            # Guardar resultado en 'res'
            resultado += f"    MOV {res}, AX\n"
            
        elif op == '-':
            if arg2 is None: # Negación unaria (ej: -variable)
                # Cargar el operando en AX
                if isinstance(arg1, int):
                    resultado += f"    MOV AX, {arg1}\n"
                else:
                    resultado += f"    MOV AX, {arg1}\n"
                # Negar AX
                resultado += f"    NEG AX\n"
                # Guardar resultado
                resultado += f"    MOV {res}, AX\n"
            else: # Resta binaria (ej: a - b)
                # Cargar arg1 en AX
                if isinstance(arg1, int):
                    resultado += f"    MOV AX, {arg1}\n"
                else:
                    resultado += f"    MOV AX, {arg1}\n"
                
                # Restar arg2 de AX
                if isinstance(arg2, int):
                    resultado += f"    SUB AX, {arg2}\n"
                else:
                    resultado += f"    SUB AX, {arg2}\n"
                
                # Guardar resultado en 'res'
                resultado += f"    MOV {res}, AX\n"
            
        elif op == '*':
            # Multiplicación (ej: a * b)
            # Cargar arg1 en AX
            if isinstance(arg1, int):
                resultado += f"    MOV AX, {arg1}\n"
            else:
                resultado += f"    MOV AX, {arg1}\n"
            
            # Cargar arg2 en BX (IMUL usa BX para el multiplicador)
            if isinstance(arg2, int):
                resultado += f"    MOV BX, {arg2}\n"
            else:
                resultado += f"    MOV BX, {arg2}\n"
            
            # Realizar multiplicación: AX * BX -> DX:AX (resultado en AX para 16-bit)
            resultado += f"    IMUL BX\n"
            
            # Guardar resultado en 'res' (solo la parte baja del resultado en AX)
            resultado += f"    MOV {res}, AX\n"
            
        elif op == '/':
            # División (ej: a / b)
            # Cargar dividendo en AX
            if isinstance(arg1, int):
                resultado += f"    MOV AX, {arg1}\n"
            else:
                resultado += f"    MOV AX, {arg1}\n"
            
            # Extender signo de AX a DX para la división (para manejar números negativos)
            resultado += f"    CWD              ; Extender signo de AX a DX\n"
            
            # Cargar divisor en BX
            if isinstance(arg2, int):
                resultado += f"    MOV BX, {arg2}\n"
            else:
                resultado += f"    MOV BX, {arg2}\n"
            
            # Realizar división: DX:AX / BX -> AX (cociente), DX (resto)
            resultado += f"    IDIV BX\n"
            
            # Guardar cociente en 'res'
            resultado += f"    MOV {res}, AX\n"
            
        elif op == 'impcad':
            # Imprimir cadena literal o variable de cadena
            if isinstance(arg1, str) and arg1.startswith('"'): # Cadena literal
                if arg1 in cadenas_literales:
                    label = cadenas_literales[arg1]
                    resultado += f"    LEA DX, {label}\n"
                else: # Cadena literal no encontrada (esto no debería pasar si se procesó correctamente)
                    resultado += f"    ; Error: Cadena '{arg1}' no definida en .DATA\n"
            elif arg1: # Variable de cadena (se asume que arg1 es el nombre de la variable)
                # Para emu8086, imprimir una cadena de variable requiere que termine con '$'
                # Aquí asumimos que las variables de cadena ya están preparadas en .DATA
                resultado += f"    LEA DX, {arg1}\n"
            else:
                resultado += f"    ; Aviso: Se intenta imprimir una cadena vacía o no especificada.\n"
            
            # Llamar a la interrupción DOS para imprimir cadena
            resultado += f"    MOV AH, 09h\n"
            resultado += f"    INT 21h\n"
            
            # Imprimir salto de línea después de la cadena
            resultado += f"    LEA DX, newline\n"
            resultado += f"    MOV AH, 09h\n"
            resultado += f"    INT 21h\n"
            
        elif op == 'impdig':
            # Imprimir entero
            # Cargar el valor a imprimir en AX
            if isinstance(arg1, int):
                resultado += f"    MOV AX, {arg1}\n"
            elif isinstance(arg1, str) and arg1.startswith('"'):
                # Error: se intenta imprimir cadena con impdig
                resultado += f"    ; Error: impdig espera un entero, no una cadena literal.\n"
                continue
            else: # Variable o temporal
                resultado += f"    MOV AX, {arg1}\n"
            
            # Llamar a la rutina de impresión de números
            resultado += f"    CALL PRINT_NUM\n"
            
            # Imprimir salto de línea
            resultado += f"    LEA DX, newline\n"
            resultado += f"    MOV AH, 09h\n"
            resultado += f"    INT 21h\n"
            
        elif op == 'leerdig':
            # Leer entero y asignarlo a la variable 'res'
            # Llamar a la rutina de lectura de números
            resultado += f"    CALL READ_NUM\n"
            # El resultado de READ_NUM está en AX, asignarlo a 'res'
            resultado += f"    MOV {res}, AX\n"
            
        elif op == 'label':
            # Generar etiqueta para saltos
            resultado += f"{res}:\n"
            
        elif op == 'goto':
            # Salto incondicional
            resultado += f"    JMP {res}\n"
            
        elif op == 'if_false':
            # Salto condicional: si la condición es falsa (0), salta a 'res'
            # Cargar la condición en AX
            if isinstance(arg1, int):
                resultado += f"    MOV AX, {arg1}\n"
            else: # Variable o temporal
                resultado += f"    MOV AX, {arg1}\n"
            
            # Comparar AX con 0
            resultado += f"    CMP AX, 0\n"
            # Saltar si es igual a cero (falso)
            resultado += f"    JE {res}\n"
        
        resultado += "\n" # Espacio entre cuádruplos generados
    
    # Finalizar programa
    resultado += "    ; Terminar programa\n"
    resultado += "    MOV AH, 4Ch\n"
    resultado += "    INT 21h\n"
    resultado += "MAIN ENDP\n\n"
    
    # Procedimientos auxiliares
    resultado += "; ═══════════════════════════════════════════════════════════\n"
    resultado += "; PROCEDIMIENTOS AUXILIARES\n"
    resultado += "; ═══════════════════════════════════════════════════════════\n\n"
    
    # Procedimiento para imprimir número (entero de 16 bits)
    resultado += "PRINT_NUM PROC\n"
    resultado += "    ; Imprime el número entero positivo o negativo en AX\n"
    resultado += "    PUSH AX\n"
    resultado += "    PUSH BX\n"
    resultado += "    PUSH CX\n"
    resultado += "    PUSH DX\n\n"
    resultado += "    MOV CX, 0         ; Contador de dígitos\n"
    resultado += "    MOV BX, 10        ; Base para la división\n"
    
    resultado += "    CMP AX, 0\n"
    resultado += "    JGE PRINT_POSITIVE\n"
    
    # Manejo de números negativos
    resultado += "    ; Número negativo\n"
    resultado += "    PUSH AX           ; Guardar el número negativo original\n"
    resultado += "    MOV DL, '-'\n"
    resultado += "    MOV AH, 02h       ; Función DOS para imprimir caracter\n"
    resultado += "    INT 21h\n"
    resultado += "    POP AX            ; Recuperar el número negativo\n"
    resultado += "    NEG AX            ; Hacerlo positivo para la división\n\n"
    
    resultado += "PRINT_POSITIVE:\n"
    resultado += "    ; Proceso de división para obtener dígitos\n"
    resultado += "    MOV DX, 0         ; Limpiar DX para la división (DX:AX)\n"
    resultado += "    DIV BX            ; AX = AX / 10, DX = AX % 10 (resto)\n"
    resultado += "    PUSH DX           ; Guardar el resto (dígito) en la pila\n"
    resultado += "    INC CX            ; Incrementar contador de dígitos\n"
    resultado += "    CMP AX, 0         ; ¿Cociente es cero?\n"
    resultado += "    JNE PRINT_POSITIVE ; Si no, continuar dividiendo\n\n"
    
    resultado += "PRINT_LOOP:\n"
    resultado += "    ; Sacar dígitos de la pila y convertirlos a caracter ASCII\n"
    resultado += "    POP DX\n"
    resultado += "    ADD DL, '0'       ; Convertir dígito (0-9) a caracter ASCII ('0'-'9')\n"
    resultado += "    MOV AH, 02h       ; Función DOS para imprimir caracter\n"
    resultado += "    INT 21h\n"
    resultado += "    LOOP PRINT_LOOP   ; Repetir hasta que CX sea 0\n\n"
    
    resultado += "    ; Restaurar registros\n"
    resultado += "    POP DX\n"
    resultado += "    POP CX\n"
    resultado += "    POP BX\n"
    resultado += "    POP AX\n"
    resultado += "    RET               ; Retornar de la subrutina\n"
    resultado += "PRINT_NUM ENDP\n\n"
    
    # Procedimiento para leer número (entero de 16 bits)
    resultado += "READ_NUM PROC\n"
    resultado += "    ; Lee una secuencia de dígitos ASCII desde la entrada estándar\n"
    resultado += "    ; y la convierte en un número entero de 16 bits, retornando en AX.\n"
    resultado += "    PUSH BX\n"
    resultado += "    PUSH CX\n"
    resultado += "    PUSH DX\n\n"
    
    resultado += "    MOV BX, 0         ; Acumulador del número (inicialmente 0)\n"
    resultado += "    MOV CX, 10        ; Multiplicador (para formar el número: num = num * 10 + digito)\n\n"
    
    resultado += "READ_LOOP:\n"
    resultado += "    MOV AH, 01h       ; Función DOS para leer caracter con eco\n"
    resultado += "    INT 21h\n"
    resultado += "    CMP AL, 0Dh       ; ¿Es la tecla Enter (Carriage Return)?\n"
    resultado += "    JE READ_DONE      ; Si es Enter, finalizar lectura\n\n"
    
    resultado += "    ; Convertir caracter ASCII a dígito numérico\n"
    resultado += "    SUB AL, '0'\n"
    resultado += "    MOV AH, 0         ; Limpiar AH para tener el dígito en AX\n"
    
    resultado += "    ; Calcular: BX = BX * 10 + AX (nuevo dígito)\n"
    resultado += "    PUSH AX           ; Guardar el dígito temporalmente\n"
    resultado += "    MOV AX, BX        ; Mover el acumulador a AX para la multiplicación\n"
    resultado += "    MUL CX            ; AX = AX * 10\n"
    resultado += "    MOV BX, AX        ; Guardar resultado intermedio en BX\n"
    resultado += "    POP AX            ; Recuperar el dígito\n"
    resultado += "    ADD BX, AX        ; Sumar el dígito al resultado intermedio\n\n"
    
    resultado += "    JMP READ_LOOP     ; Continuar leyendo el siguiente caracter\n\n"
    
    resultado += "READ_DONE:\n"
    resultado += "    MOV AX, BX        ; El número final está en BX, pasarlo a AX para retornar\n\n"
    
    resultado += "    ; Restaurar registros\n"
    resultado += "    POP DX\n"
    resultado += "    POP CX\n"
    resultado += "    POP BX\n"
    resultado += "    RET               ; Retornar de la subrutina\n"
    resultado += "READ_NUM ENDP\n\n"
    
    resultado += "END MAIN\n"
    resultado += "; ═══════════════════════════════════════════════════════════\n"
    resultado += "; FIN DEL PROGRAMA\n"
    resultado += "; ═══════════════════════════════════════════════════════════\n"
    
    return resultado

def generar_codigo_fuente():
    """Genera el reporte completo de cuádruplos y código ensamblador"""
    if not cuadruplos_globales:
        return "⚠️ No se generaron cuádruplos.\n"
    
    resultado = "╔═══════════════════════════════════════════════════════════╗\n"
    resultado += "║                  CUÁDRUPLOS GENERADOS                     ║\n"
    resultado += "╚═══════════════════════════════════════════════════════════╝\n\n"
    
    resultado += f"{'#':<5} {'Operador':<12} {'Arg1':<12} {'Arg2':<12} {'Resultado':<12}\n"
    resultado += "─" * 60 + "\n"
    for i, cuad in enumerate(cuadruplos_globales, 1):
        op, arg1, arg2, res = cuad
        arg1_str = str(arg1) if arg1 is not None else '─'
        arg2_str = str(arg2) if arg2 is not None else '─'
        res_str = str(res) if res is not None else '─'
        resultado += f"{i:<5} {op:<12} {arg1_str:<12} {arg2_str:<12} {res_str:<12}\n"
    
    resultado += "\n" + "═" * 60 + "\n\n"
    resultado += generar_codigo_ensamblador_emu8086()
    
    return resultado

# ================= INTERFAZ GRÁFICA MEJORADA =================
class AnalizadorGUI:
    """Interfaz gráfica mejorada del compilador"""
    def __init__(self, root):
        self.root = root
        self.root.title("Compilador PF2024 - Automatas 2 | Análisis Completo")
        self.root.geometry("1500x950")
        
        style = ttk.Style()
        style.theme_use('clam')
        
        self.color_bg = "#f5f6fa"
        self.color_primary = "#2c3e50"
        self.color_secondary = "#34495e"
        self.color_success = "#27ae60"
        self.color_error = "#e74c3c"
        self.color_warning = "#f39c12"
        self.color_info = "#3498db"
        self.color_accent = "#9b59b6"
        
        self.root.configure(bg=self.color_bg)
        
        self.crear_barra_superior()
        self.crear_area_trabajo()
        self.crear_barra_estado()
    
    def crear_barra_superior(self):
        """Crea la barra superior con título y botones principales"""
        barra = tk.Frame(self.root, bg=self.color_primary, height=90)
        barra.pack(fill='x', side='top')
        
        # Título con icono
        titulo_frame = tk.Frame(barra, bg=self.color_primary)
        titulo_frame.pack(side='left', padx=20, pady=10)
        
        titulo = tk.Label(titulo_frame, text="⚙️ COMPILADOR PF2024", 
                         font=('Segoe UI', 22, 'bold'), 
                         bg=self.color_primary, fg='white')
        titulo.pack(anchor='w')
        
        subtitulo = tk.Label(titulo_frame, 
                            text="Análisis Léxico • Sintáctico • Semántico • Generación de Código", 
                            font=('Segoe UI', 10), 
                            bg=self.color_primary, fg='#ecf0f1')
        subtitulo.pack(anchor='w')
        
        # Botones principales con iconos
        btn_frame = tk.Frame(barra, bg=self.color_primary)
        btn_frame.pack(side='right', padx=20)
        
        btn_analizar = tk.Button(btn_frame, text="▶ Analizar", 
                                command=self.analizar,
                                bg=self.color_success, fg='white',
                                font=('Segoe UI', 11, 'bold'),
                                padx=25, pady=10, relief='flat',
                                cursor='hand2', borderwidth=0)
        btn_analizar.pack(side='left', padx=5)
        
        btn_guardar_asm = tk.Button(btn_frame, text="💾 Guardar ASM", 
                                    command=self.guardar_asm,
                                    bg=self.color_info, fg='white',
                                    font=('Segoe UI', 11, 'bold'),
                                    padx=20, pady=10, relief='flat',
                                    cursor='hand2', borderwidth=0)
        btn_guardar_asm.pack(side='left', padx=5)
        
        btn_limpiar = tk.Button(btn_frame, text="🗑️ Limpiar", 
                               command=self.limpiar_todo,
                               bg=self.color_warning, fg='white',
                               font=('Segoe UI', 11, 'bold'),
                               padx=20, pady=10, relief='flat',
                               cursor='hand2', borderwidth=0)
        btn_limpiar.pack(side='left', padx=5)
        
        btn_cargar = tk.Button(btn_frame, text="📁 Cargar", 
                              command=self.cargar_archivo,
                              bg=self.color_accent, fg='white',
                              font=('Segoe UI', 11, 'bold'),
                              padx=20, pady=10, relief='flat',
                              cursor='hand2', borderwidth=0)
        btn_cargar.pack(side='left', padx=5)
    
    def crear_area_trabajo(self):
        """Crea el área de trabajo con pestañas"""
        container = tk.Frame(self.root, bg=self.color_bg)
        container.pack(fill='both', expand=True, padx=15, pady=10)
        
        # Panel izquierdo - Editor de código
        panel_izq = tk.Frame(container, bg='white', relief='solid', borderwidth=1)
        panel_izq.pack(side='left', fill='both', expand=True, padx=(0, 7))
        
        titulo_editor_frame = tk.Frame(panel_izq, bg=self.color_secondary, height=40)
        titulo_editor_frame.pack(fill='x')
        titulo_editor_frame.pack_propagate(False)
        
        titulo_editor = tk.Label(titulo_editor_frame, text="📝 Editor de Código Fuente", 
                                font=('Segoe UI', 12, 'bold'),
                                bg=self.color_secondary, fg='white')
        titulo_editor.pack(pady=10)
        
        # Editor de código con números de línea
        editor_frame = tk.Frame(panel_izq, bg='white')
        editor_frame.pack(fill='both', expand=True, padx=10, pady=10)
        
        self.codigo_text = scrolledtext.ScrolledText(editor_frame, 
                                                     height=28, 
                                                     font=('Consolas', 11),
                                                     wrap=tk.NONE,
                                                     bg='#ffffff',
                                                     fg='#2c3e50',
                                                     insertbackground='#2c3e50',
                                                     selectbackground='#d4e6f1',
                                                     selectforeground='#2c3e50',
                                                     padx=10, pady=10)
        self.codigo_text.pack(fill='both', expand=True)

        # Código de ejemplo mejorado
        codigo_ejemplo = '''pf2024 MiPrograma
decl
Int a, b, resultado;
Cad mensaje;

Inicio
    // Asignaciones básicas
    a := 10;
    b := 5;
    
    // Operaciones aritméticas
    resultado := a + b * 2;
    
    // Entrada/Salida
    mensaje := "Hola desde PF2024";
    impcad(mensaje);
    impdig(resultado);
    
    // Lectura de datos
    leerdig(a);
    impdig(a);
Fin'''
        self.codigo_text.insert('1.0', codigo_ejemplo)
        
        # Panel derecho - Resultados con pestañas
        panel_der = tk.Frame(container, bg='white', relief='solid', borderwidth=1)
        panel_der.pack(side='right', fill='both', expand=True, padx=(7, 0))
        
        style = ttk.Style()
        style.configure('TNotebook', background=self.color_bg)
        style.configure('TNotebook.Tab', padding=[20, 10], font=('Segoe UI', 10, 'bold'))
        
        self.notebook = ttk.Notebook(panel_der)
        self.notebook.pack(fill='both', expand=True, padx=5, pady=5)
        
        # Crear pestañas
        self.crear_pestana_simbolos()
        self.crear_pestana_codigo_intermedio()
        self.crear_pestana_semantico()
        self.crear_pestana_cuadruplos()
        self.crear_pestana_errores()
        
    def crear_pestana_simbolos(self):
        """Pestaña de tabla de símbolos"""
        frame = ttk.Frame(self.notebook)
        self.notebook.add(frame, text="📊 Tabla de Símbolos")
        
        style = ttk.Style()
        style.configure("Treeview", font=('Consolas', 10), rowheight=25)
        style.configure("Treeview.Heading", font=('Segoe UI', 10, 'bold'))
        
        columns = ('No.', 'Lexema', 'Token', 'Referencia')
        self.tabla_tree = ttk.Treeview(frame, columns=columns, show='headings', height=25)
        
        for col in columns:
            self.tabla_tree.heading(col, text=col)
            self.tabla_tree.column(col, width=140, anchor='center')
        
        self.tabla_tree.pack(fill='both', expand=True, padx=10, pady=10)
        
        scrollbar = ttk.Scrollbar(frame, orient=tk.VERTICAL, command=self.tabla_tree.yview)
        scrollbar.pack(side='right', fill='y')
        self.tabla_tree.configure(yscrollcommand=scrollbar.set)
    
    def crear_pestana_codigo_intermedio(self):
        """Pestaña de código intermedio"""
        frame = ttk.Frame(self.notebook)
        self.notebook.add(frame, text="🔄 Código Intermedio")
        
        self.intermedio_text = scrolledtext.ScrolledText(frame, 
                                                         height=32, 
                                                         font=('Consolas', 10),
                                                         bg='#fafafa',
                                                         fg='#2c3e50',
                                                         padx=10, pady=10,
                                                         state='normal')
        self.intermedio_text.pack(fill='both', expand=True, padx=10, pady=10)
    
    def crear_pestana_semantico(self):
        """Pestaña de análisis semántico"""
        frame = ttk.Frame(self.notebook)
        self.notebook.add(frame, text="🔍 Análisis Semántico")
        
        self.semantico_text = scrolledtext.ScrolledText(frame, 
                                                        height=32, 
                                                        font=('Consolas', 10),
                                                        bg='#fafafa',
                                                        fg='#2c3e50',
                                                        padx=10, pady=10,
                                                        state='normal')
        self.semantico_text.pack(fill='both', expand=True, padx=10, pady=10)
    
    def crear_pestana_cuadruplos(self):
        """Pestaña de cuádruplos y ensamblador"""
        frame = ttk.Frame(self.notebook)
        self.notebook.add(frame, text="⚙️ Cuádruplos & ASM")
        
        self.cuadruplos_text = scrolledtext.ScrolledText(frame, 
                                                         height=32, 
                                                         font=('Consolas', 9),
                                                         bg='#fafafa',
                                                         fg='#2c3e50',
                                                         padx=10, pady=10,
                                                         state='normal')
        self.cuadruplos_text.pack(fill='both', expand=True, padx=10, pady=10)
    
    def crear_pestana_errores(self):
        """Pestaña de errores"""
        frame = ttk.Frame(self.notebook)
        self.notebook.add(frame, text="⚠️ Errores")
        
        self.errores_text = scrolledtext.ScrolledText(frame, 
                                                      height=32, 
                                                      font=('Consolas', 10),
                                                      bg='#fff5f5',
                                                      fg='#c0392b',
                                                      padx=10, pady=10,
                                                      state='normal')
        self.errores_text.pack(fill='both', expand=True, padx=10, pady=10)

    def crear_barra_estado(self):
        """Crea la barra de estado en la parte inferior"""
        self.barra_estado = tk.Frame(self.root, bg=self.color_secondary, height=30)
        self.barra_estado.pack(fill='x', side='bottom')
        
        self.label_estado = tk.Label(self.barra_estado, 
                                     text="✓ Listo para analizar", 
                                     font=('Segoe UI', 9),
                                     bg=self.color_secondary, 
                                     fg='white',
                                     anchor='w')
        self.label_estado.pack(side='left', padx=15, pady=5)
        
        self.label_info = tk.Label(self.barra_estado, 
                                   text="", 
                                   font=('Segoe UI', 9),
                                   bg=self.color_secondary, 
                                   fg='#ecf0f1',
                                   anchor='e')
        self.label_info.pack(side='right', padx=15, pady=5)

    def actualizar_estado(self, mensaje, tipo='info'):
        """Actualiza la barra de estado"""
        iconos = {
            'info': '✓',
            'warning': '⚠️',
            'error': '❌',
            'processing': '⏳'
        }
        icono = iconos.get(tipo, '✓')
        self.label_estado.config(text=f"{icono} {mensaje}")
        self.root.update()

    def analizar(self):
        """Ejecuta el análisis completo del código"""
        self.actualizar_estado("Analizando código...", 'processing')
        reiniciar_datos()
        
        # Cambiado a habilitar edición temporalmente para limpiar y actualizar
        # Limpiar todas las áreas de texto
        self.errores_text.config(state='normal')
        self.errores_text.delete('1.0', tk.END)
        
        self.intermedio_text.config(state='normal')
        self.intermedio_text.delete('1.0', tk.END)
        
        self.semantico_text.config(state='normal')
        self.semantico_text.delete('1.0', tk.END)
        
        self.cuadruplos_text.config(state='normal')
        self.cuadruplos_text.delete('1.0', tk.END)
        
        codigo = self.codigo_text.get('1.0', tk.END)
        global lineas_codigo
        lineas_codigo = codigo.split('\n')
        
        try:
            # Análisis léxico y sintáctico
            self.reiniciar_lexer()
            analizador_lexico.input(codigo)
            self.reiniciar_lexer()
            analizador_lexico.input(codigo)
            parser.parse(lexer=analizador_lexico)
            
            # Actualizar resultados
            self.actualizar_tabla()
            self.intermedio_text.insert('1.0', generar_codigo_intermedio_formateado())
            self.semantico_text.insert('1.0', generar_reporte_semantico())
            self.cuadruplos_text.insert('1.0', generar_codigo_fuente())
            
            # Cambiado a deshabilitar edición después de actualizar contenido
            self.intermedio_text.config(state='disabled')
            self.semantico_text.config(state='disabled')
            self.cuadruplos_text.config(state='disabled')
            
            total_errores = len(errores) + len(errores_semanticos)
            
            if errores or errores_semanticos:
                self.errores_text.insert(tk.END, "╔═══════════════════════════════════════════════════════════╗\n")
                self.errores_text.insert(tk.END, "║                  ⚠️ ERRORES ENCONTRADOS                   ║\n")
                self.errores_text.insert(tk.END, "╚═══════════════════════════════════════════════════════════╝\n\n")
                
                if errores:
                    self.errores_text.insert(tk.END, "┌─ ERRORES LÉXICOS Y SINTÁCTICOS ─────────────────────────┐\n")
                    for i, error in enumerate(errores, 1):
                        self.errores_text.insert(tk.END, f"│ ❌ Error #{i}:\n")
                        self.errores_text.insert(tk.END, f"│   📍 Línea: {error['line']}\n")
                        self.errores_text.insert(tk.END, f"│   🏷️  Tipo: {error['type']}\n")
                        self.errores_text.insert(tk.END, f"│   📝 {error['desc']}\n")
                        if 'sugerencia' in error:
                            self.errores_text.insert(tk.END, f"│   💡 Sugerencia: {error['sugerencia']}\n")
                        self.errores_text.insert(tk.END, "│\n")
                    self.errores_text.insert(tk.END, "└" + "─"*58 + "┘\n\n")
                
                if errores_semanticos:
                    self.errores_text.insert(tk.END, "┌─ ERRORES SEMÁNTICOS ────────────────────────────────────┐\n")
                    for i, error in enumerate(errores_semanticos, 1):
                        self.errores_text.insert(tk.END, f"│ ❌ Error #{i}:\n")
                        self.errores_text.insert(tk.END, f"│   📍 Línea: {error.linea}\n")
                        self.errores_text.insert(tk.END, f"│   🏷️  Tipo: {error.tipo}\n")
                        self.errores_text.insert(tk.END, f"│   📝 {error.descripcion}\n")
                        self.errores_text.insert(tk.END, f"│   📄 Contexto: {error.contexto}\n")
                        if error.sugerencia:
                            self.errores_text.insert(tk.END, f"│   💡 Sugerencia: {error.sugerencia}\n")
                        self.errores_text.insert(tk.END, "│\n")
                    self.errores_text.insert(tk.END, "└" + "─"*58 + "┘\n")
                
                # Cambiado a deshabilitar edición en errores
                self.errores_text.config(state='disabled')
                
                self.actualizar_estado(f"Análisis completado con {total_errores} errores", 'warning')
                self.label_info.config(text=f"Errores: {total_errores} | Variables: {len(analizador_sem.variables)}")
                messagebox.showwarning("Análisis Completado", 
                                      f"⚠️ Se encontraron {total_errores} errores.\n\nRevise la pestaña de Errores para más detalles.")
            else:
                self.errores_text.insert(tk.END, "╔═══════════════════════════════════════════════════════════╗\n")
                self.errores_text.insert(tk.END, "║              ✅ ANÁLISIS EXITOSO                          ║\n")
                self.errores_text.insert(tk.END, "╚═══════════════════════════════════════════════════════════╝\n\n")
                self.errores_text.insert(tk.END, "✓ No se encontraron errores léxicos\n")
                self.errores_text.insert(tk.END, "✓ No se encontraron errores sintácticos\n")
                self.errores_text.insert(tk.END, "✓ No se encontraron errores semánticos\n\n")
                self.errores_text.insert(tk.END, "El código está listo para ser compilado.\n")
                self.errores_text.insert(tk.END, "Puede guardar el archivo .asm desde el botón 'Guardar ASM'.\n")
                
                # Cambiado a deshabilitar edición en errores
                self.errores_text.config(state='disabled')
                
                self.actualizar_estado("Análisis completado exitosamente", 'info')
                self.label_info.config(text=f"Variables: {len(analizador_sem.variables)} | Cuádruplos: {len(cuadruplos_globales)}")
                messagebox.showinfo("✅ Éxito", "¡Análisis completado sin errores!\n\nEl código ensamblador está listo.")
                
        except Exception as e:
            self.errores_text.insert(tk.END, f"❌ Error crítico durante el análisis:\n\n{str(e)}\n")
            # Cambiado a deshabilitar edición en errores
            self.errores_text.config(state='disabled')
            self.actualizar_estado("Error crítico en el análisis", 'error')
            messagebox.showerror("Error", f"Error durante el análisis:\n{str(e)}")
    
    def guardar_asm(self):
        """Guarda el código ensamblador en un archivo .asm"""
        if not cuadruplos_globales:
            messagebox.showwarning("Advertencia", "⚠️ No hay código ensamblador para guardar.\n\nPrimero debe analizar el código.")
            return
        
        if errores or errores_semanticos:
            respuesta = messagebox.askyesno("Errores Detectados", 
                                           "⚠️ El código tiene errores.\n\n¿Desea guardar el archivo .asm de todas formas?")
            if not respuesta:
                return
        
        # Diálogo para guardar archivo
        archivo = filedialog.asksaveasfilename(
            title="Guardar archivo ensamblador",
            defaultextension=".asm",
            initialfile=f"{nombre_programa}.asm",
            filetypes=[("Archivos ASM", "*.asm"), ("Todos los archivos", "*.*")]
        )
        
        if archivo:
            try:
                codigo_asm = generar_codigo_ensamblador_emu8086()
                with open(archivo, 'w', encoding='utf-8') as f:
                    f.write(codigo_asm)
                
                self.actualizar_estado(f"Archivo guardado: {os.path.basename(archivo)}", 'info')
                messagebox.showinfo("✅ Éxito", 
                                   f"Archivo guardado exitosamente:\n\n{archivo}\n\n"
                                   f"Puede abrirlo en emu8086 para ejecutarlo.")
            except Exception as e:
                self.actualizar_estado("Error al guardar archivo", 'error')
                messagebox.showerror("Error", f"Error al guardar el archivo:\n{str(e)}")
    
    def actualizar_tabla(self):
        """Actualiza la tabla de símbolos"""
        for item in self.tabla_tree.get_children():
            self.tabla_tree.delete(item)
        for simbolo in tabla_simbolos:
            self.tabla_tree.insert('', 'end', values=(
                simbolo.numero, simbolo.lexema, simbolo.token, simbolo.referencia or ''
            ))
    
    def limpiar_todo(self):
        """Limpia todos los resultados"""
        reiniciar_datos()
        self.actualizar_tabla()
        
        # Cambiado a habilitar edición temporalmente para limpiar
        self.errores_text.config(state='normal')
        self.errores_text.delete('1.0', tk.END)
        self.errores_text.config(state='disabled')
        
        self.intermedio_text.config(state='normal')
        self.intermedio_text.delete('1.0', tk.END)
        self.intermedio_text.config(state='disabled')
        
        self.semantico_text.config(state='normal')
        self.semantico_text.delete('1.0', tk.END)
        self.semantico_text.config(state='disabled')
        
        self.cuadruplos_text.config(state='normal')
        self.cuadruplos_text.delete('1.0', tk.END)
        self.cuadruplos_text.config(state='disabled')
        
        self.actualizar_estado("Resultados limpiados", 'info')
        self.label_info.config(text="")
        messagebox.showinfo("Limpieza", "✓ Todos los resultados han sido limpiados.")

    def cargar_archivo(self):
        """Carga un archivo de código"""
        file_path = filedialog.askopenfilename(
            title="Seleccionar archivo",
            filetypes=[("Archivos PF2024", "*.pf"), ("Archivos de texto", "*.txt"), ("Todos", "*.*")]
        )
        if file_path:
            try:
                with open(file_path, 'r', encoding='utf-8') as file:
                    self.codigo_text.delete('1.0', tk.END)
                    self.codigo_text.insert('1.0', file.read())
                self.actualizar_estado(f"Archivo cargado: {os.path.basename(file_path)}", 'info')
                messagebox.showinfo("✅ Éxito", f"Archivo cargado:\n{file_path}")
            except Exception as e:
                self.actualizar_estado("Error al cargar archivo", 'error')
                messagebox.showerror("Error", f"Error al cargar el archivo:\n{str(e)}")

    def reiniciar_lexer(self):
        """Reinicia el analizador léxico"""
        analizador_lexico.lineno = 1
        analizador_lexico.lexpos = 0

# ================= PUNTO DE ENTRADA =================
if __name__ == "__main__":
    print("="*70)
    print("COMPILADOR - AUTOMATAS 2")
    print("Análisis Léxico, Sintáctico, Semántico y Generación de Código")
    print("="*70)
    root = tk.Tk()
    app = AnalizadorGUI(root)
    root.mainloop()
